{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# EXT      InlineAll              #-}

module Text.Parsert where

import qualified Prelude as P
import qualified Data.List as List
import Prologue hiding (catch)

import Control.Monad.State.Layered


---------------------------
-- === Error parsing === --
---------------------------


-- === Definition === --

type family Error (m :: * -> *) :: *

class Monad m => MonadThrowParser m where
    throw :: forall a. Error m -> m a

class Monad m => MonadErrorBuilder t m e where
    buildError :: t -> m e

type MonadErrorParser t m = (MonadThrowParser m, MonadErrorBuilder t m (Error m))


-- === Utils === --

raise :: MonadErrorParser t m => t -> m a
raise = buildError >=> throw


-- === Primitive errors === --

newtype UncaughtError = UncaughtError String deriving (Show)
instance (Monad m, Show t) => MonadErrorBuilder t m UncaughtError where
    buildError = return . UncaughtError . show


-- === Instances === --

type instance Error (StateT s m) = Error m
instance MonadThrowParser m => MonadThrowParser (StateT s m) where
    throw = lift . throw



------------------------------
-- === Progress parsing === --
------------------------------

-- === Definition === --

newtype Progress = Progress Bool deriving (Show)
makeLenses ''Progress

class Monad m => MonadProgressParser m where
    putProgress :: Bool -> m ()
    getProgress :: m Bool
    try         :: m a -> m a

    default putProgress :: (m ~ t n, MonadTrans t, MonadProgressParser n) => Bool -> m ()
    default getProgress :: (m ~ t n, MonadTrans t, MonadProgressParser n) => m Bool
    putProgress = lift . putProgress
    getProgress = lift   getProgress

class Monad m => MonadCatchParser m where
    catch :: m a -> m (Either (Error m) a)


-- === Utils === --

recover :: MonadCatchParser m => (Error m -> m a) -> m a -> m a
recover f m = catch m >>= \case
    Right a -> return a
    Left  e -> f e

recover_ :: MonadCatchParser m => (Error m -> m a) -> m b -> m ()
recover_ f m = recover (void . f) (void m)

setProgress :: MonadProgressParser m => m ()
setProgress = putProgress True

unsetProgress :: MonadProgressParser m => m ()
unsetProgress = putProgress False


-- === Instances === --

instance {-# OVERLAPPABLE #-} MonadProgressParser m
 => MonadProgressParser (StateT s m) where
    try = mapStateT try

instance {-# OVERLAPPABLE #-} MonadCatchParser m
 => MonadCatchParser (StateT s m) where
     catch ma = stateT $ \s -> catch (runStateT ma s)
               <&> \case Left  e      -> (Left  e, s)
                         Right (a, t) -> (Right a, t)



---------------------------
-- === Token parsing === --
---------------------------

-- === Definition === --

type family Token (m :: * -> *) :: *

class Monad m => MonadTokenParser m where
    lookupToken :: m (Maybe (Token m))
    default lookupToken :: (m ~ t m', Token m' ~ Token (t m'), MonadTokenParser m', MonadTrans t, Monad m') => m (Maybe (Token m))
    lookupToken = lift lookupToken


-- === Utils === --

takeToken :: (MonadTokenParser m, MonadErrorParser EmptyStreamError m) => m (Token m)
takeToken = maybe (raise EmptyStreamError) return =<< lookupToken

anyToken :: (MonadTokenParser m, MonadErrorParser EmptyStreamError m, MonadProgressParser m) => m (Token m)
anyToken = takeToken <* setProgress

dropToken :: (MonadTokenParser m, MonadErrorParser EmptyStreamError m, MonadProgressParser m) => m ()
dropToken = void anyToken

token :: (MonadTokenParser m, MonadProgressParser m, Alternative m, Eq (Token m), MonadErrorParser SatisfyError m, MonadErrorParser EmptyStreamError m) => Token m -> m (Token m)
token = satisfy . (==)

satisfy :: (MonadTokenParser m, MonadProgressParser m, Alternative m, MonadErrorParser SatisfyError m, MonadErrorParser EmptyStreamError m) => (Token m -> Bool) -> m (Token m)
satisfy f = takeToken >>= \tok -> if f tok
    then tok <$ setProgress
    else raise SatisfyError

data SatisfyError     = SatisfyError     deriving (Show)
data EmptyStreamError = EmptyStreamError deriving (Show)



---------------------------
-- === Offset parser === --
---------------------------

-- === Definition === --

newtype Offset = Offset Word64 deriving (Show, Num, Enum)
makeLenses ''Offset


-- === Running === --

evalOffsetRegister :: Monad m => StateT Offset m a -> m a
evalOffsetRegister = flip evalStateT (def :: Offset)


-- === Instances === --

instance Default   Offset where def    = mempty
instance Mempty    Offset where mempty = Offset 0
instance Semigroup Offset where (<>)   = (+)

type instance Token (StateT Offset m) = Token m
instance MonadTokenParser m => MonadTokenParser (StateT Offset m) where
    lookupToken = modify_ @Offset succ >> lift lookupToken



---------------------------
-- === Stream parser === --
---------------------------

-- === Definition === --

newtype Stream s = Stream [s] deriving (Show, Functor, Foldable, Traversable, Default, Mempty, Semigroup, P.Monoid)
makeLenses ''Stream


-- === Utils === --

evalStreamProvider :: Monad m => [s] -> StateT (Stream s) m a -> m a
evalStreamProvider s = flip evalStateT $ Stream s

splitStream :: Stream s -> Maybe (s, Stream s)
splitStream = nested wrapped List.uncons


-- === Instances === --

type instance Token (StateT (Stream s) m) = s
instance Monad m => MonadTokenParser (StateT (Stream s) m) where
    lookupToken = modify @Stream go where
        go s = case splitStream s of
            Nothing     -> (Nothing, s)
            Just (t,s') -> (Just t, s')



------------------------
-- === FailParser === --
------------------------

-- === Definition === --

newtype FailParser e m a = FailParser (EitherT e m a) deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)
makeLenses ''FailParser


-- === Running === --

failParser :: m (Either e a) -> FailParser e m a
failParser = wrap . EitherT

runFailParser :: forall e m a. Monad m => FailParser e m a -> m (Either e a)
runFailParser = runEitherT . unwrap


-- === Instances === --

type instance Token (FailParser e m) = Token m
instance (MonadProgressParser m, IsString e) => MonadPlus   (FailParser e m)
instance (MonadProgressParser m, IsString e) => Alternative (FailParser e m) where
    empty = throw "Unknown error"
    l <|> r = failParser $ do
        setProgress
        la <- runFailParser l
        p  <- getProgress
        if p || isRight la then return la else runFailParser r


type instance Error (FailParser e m) = e
instance MonadProgressParser m => MonadProgressParser (FailParser e m) where
    try m = failParser $ do
        a <- runFailParser m
        when (isLeft a) unsetProgress
        return a

instance Monad m => MonadCatchParser (FailParser e m) where catch = failParser . fmap Right . runFailParser
instance Monad m => MonadThrowParser (FailParser e m) where throw = failParser . return . Left



-------------------------
-- === BackTracker === --
-------------------------

-- === Definition === --

newtype Backtracker = Backtracker { _progress :: Bool } deriving (Show)
makeLenses ''Backtracker

instance Monad m => MonadProgressParser (StateT Backtracker m) where
    getProgress = unwrap <$> get @Backtracker
    putProgress = put @Backtracker . wrap
    try         = id


-- === Running === --

evalBacktracker :: Monad m => StateT Backtracker m a -> m a
evalBacktracker = flip evalStateT (def :: Backtracker)


-- === Instances === --

type instance Token (StateT Backtracker m) = Token m
instance Default Backtracker where def = Backtracker False



----------------------------
-- === IO parser base === --
----------------------------

type instance Error IO = UncaughtError

instance MonadProgressParser IO where
    putProgress = const $ return ()
    getProgress = return False
    try         = id

instance MonadThrowParser IO where
    throw = fail . show




----------------------------------
-- === Identity parser base === --
----------------------------------

type instance Error Identity = UncaughtError

instance MonadProgressParser Identity where
    putProgress = const $ return ()
    getProgress = return False
    try         = id

instance MonadThrowParser Identity where
    throw = error . show



------------------------------
-- === Results register === --
------------------------------

-- === Definition === --

type ResultRegister r = StateT (Results r)
newtype Results a = Results [a] deriving (Show, Functor, Foldable, Traversable, Default, Semigroup, Mempty, P.Monoid)
makeLenses ''Results

type family Result (m :: * -> *) :: * where
    Result (StateT (Results a) _) = a
    Result (t m) = Result m


-- === Utils === --

type MonadResultParser t m = (MonadResultRegister m, MonadResultBuilder t m (Result m))

addResult :: MonadResultParser t m => t -> m ()
addResult = buildResult >=> registerResult

runResultRegister  :: forall res m a . Monad m => ResultRegister res m a -> m (a, Results res)
evalResultRegister :: forall res m a . Monad m => ResultRegister res m a -> m a
execResultRegister :: forall res m a . Monad m => ResultRegister res m a -> m (Results res)
runResultRegister  = runDefStateT
evalResultRegister = evalDefStateT
execResultRegister = execDefStateT


-- === ResultRegister === --

class Monad m => MonadResultRegister m where
    registerResult :: Result m -> m ()

instance {-# OVERLAPPABLE #-} (MonadResultRegister m, Result (t m) ~ Result m, Monad (t m), MonadTrans t)
 => MonadResultRegister (t m) where
    registerResult = lift . registerResult

instance Monad m => MonadResultRegister (StateT (Results a) m) where
    registerResult res = modify_ @Results $ wrapped %~ (res:)


-- === ResultBuilder === --

class Monad m => MonadResultBuilder t m a where
    buildResult :: t -> m a

instance {-# OVERLAPPABLE #-} Monad m => MonadResultBuilder t m t where
    buildResult = return



------------------------------
-- === History register === --
------------------------------

-- === Definition === --

type HistoryRegister tok = StateT (History tok)
newtype History tok = History [tok] deriving (Functor, Foldable, Traversable, Semigroup, Mempty, P.Monoid, Default)
makeLenses ''History


-- === Running === --

runHistoryRegister  :: (tok ~ Token m, Monad m) => HistoryRegister tok m a -> m (a, History tok)
evalHistoryRegister :: (tok ~ Token m, Monad m) => HistoryRegister tok m a -> m a
execHistoryRegister :: (tok ~ Token m, Monad m) => HistoryRegister tok m a -> m (History tok)
runHistoryRegister  = runDefStateT
evalHistoryRegister = evalDefStateT
execHistoryRegister = execDefStateT


-- === Instances === --

type instance Token (StateT (History tok) m) = Token m
instance (MonadTokenParser m, tok ~ Token m) => MonadTokenParser (StateT (History tok) m) where
    lookupToken = withJustM (lift lookupToken) $ \tok -> Just tok <$ modify_ @History (wrapped %~ (tok:))

instance (Show tok) => Show (History tok) where
       showsPrec d (History toks) = showParen' d $
            showString "History " . showsPrec' (reverse toks)




-------------------------------
-- tests

data OffsetError a = OffsetError Offset a deriving (Show)

instance (Monad m, Show t) => MonadErrorBuilder t m String where
    buildError t = return $ "ERROR: " <> show t

instance (MonadState Offset m, MonadErrorBuilder t m a) => MonadErrorBuilder t m (OffsetError a) where
    buildError t = do
        off <- get @Offset
        OffsetError off <$> buildError t

instance IsString a => IsString (OffsetError a) where
    fromString = OffsetError 0 . fromString

runTest1 :: IO (Either String [Char])
runTest1 = evalBacktracker
         $ runFailParser
         $ evalStreamProvider "babbbaabab"
         $ evalOffsetRegister
         $ (many (token 'a' <|> token 'b') )
        --  $ (many (token 'a' <|> token 'b') <* token 'x')

runTest2 :: IO (Either String (Char, History Char))
runTest2 = runFailParser
         $ evalStreamProvider "babbbaabab"
         $ runHistoryRegister
         $ evalOffsetRegister
         $ ((token 'a' <|> token 'b') *> token 'a')

runTest3 :: IO (Either (OffsetError String) ())
runTest3 = evalBacktracker
         $ runFailParser @(OffsetError String)
         $ evalStreamProvider "abbbaabab"
         $ evalOffsetRegister
         $ recover_ (const dropToken) (token 'a' *> token 'a') <|> (() <$ token 'b')
        --  $ (token 'a' *> token 'a')

main :: IO ()
main = do
    print =<< runTest2
    print "---"

--
-- --
-- --
-- -- main :: IO ()
-- -- main = do
-- --     print "hello"
