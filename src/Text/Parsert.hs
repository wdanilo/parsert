{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeInType             #-}
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

runOffsetRegister :: Monad m => StateT Offset m a -> m a
runOffsetRegister = flip evalStateT (def :: Offset)


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

runStreamProvider :: Monad m => [s] -> StateT (Stream s) m a -> m a
runStreamProvider s = flip evalStateT $ Stream s

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

runBacktracker :: Monad m => StateT Backtracker m a -> m a
runBacktracker = flip evalStateT (def :: Backtracker)


-- === Instances === --

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




-------------------------------
-- tests

instance (Monad m, Show t) => MonadErrorBuilder t m String where
    buildError t = return $ "ERROR: " <> show t


runTest1 :: IO (Either String [Char])
runTest1 = runBacktracker
         $ runFailParser
         $ runStreamProvider "babbbaabab"
         $ runOffsetRegister
         $ (many (token 'a' <|> token 'b') )
        --  $ (many (token 'a' <|> token 'b') <* token 'x')

runTest2 :: IO (Either String Char)
runTest2 = runFailParser
         $ runStreamProvider "babbbaabab"
         $ runOffsetRegister
         $ (token 'a' <|> token 'b')

-- runTest3 :: IO (Either String Char)
runTest3 = runBacktracker
         $ runFailParser @String
         $ runStreamProvider "abbbaabab"
         $ runOffsetRegister
         $ recover_ (const dropToken) (token 'a' *> token 'a') <|> (() <$ token 'b')

main :: IO ()
main = do
    print =<< runTest3
    print "---"

--
-- --
-- --
-- -- main :: IO ()
-- -- main = do
-- --     print "hello"
