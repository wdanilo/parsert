{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeInType             #-}
{-# EXT      InlineAll              #-}

module Text.Parsert where

import qualified Prelude as P
import qualified Data.List as List
import Prologue

import Control.Monad.State.Layered


---------------------------
-- === Error parsing === --
---------------------------

type family Error (m :: * -> *) :: *

class Monad m => MonadThrowParser m where
    throw :: forall a. Error m -> m a

class Monad m => MonadErrorBuilder t m e where
    buildError :: t -> m e


type MonadErrorParser t m = (MonadThrowParser m, MonadErrorBuilder t m (Error m))


-- === Instances === --

type instance Error (StateT s m) = Error m
instance MonadThrowParser m => MonadThrowParser (StateT s m) where
    throw = lift . throw


raise :: MonadErrorParser t m => t -> m a
raise = buildError >=> throw



------------------------------
-- === Progress parsing === --
------------------------------

-- === Definition === --

newtype Progress = Progress Bool deriving (Show)
makeLenses ''Progress

-- We can make this definition much less powerfull by disallowing getting the current progress,
-- however it is possible by now so maybe we will find it useful somehow
class Monad m => MonadProgressParser m where
    getProgress :: m Progress
    putProgress :: Progress -> m ()
    try         :: m a -> m a

class Monad m => MonadRecoveryParser m where
    recover :: m a -> m (Either (Error m) a)


-- === Utils === --

setProgress :: MonadProgressParser m => m ()
setProgress = putProgress $ Progress True


-- === Instances === --

instance {-# OVERLAPPABLE #-} MonadProgressParser m
 => MonadProgressParser (StateT s m) where
    getProgress = lift getProgress
    putProgress = lift . putProgress
    try         = mapStateT try

instance {-# OVERLAPPABLE #-} MonadRecoveryParser m
 => MonadRecoveryParser (StateT s m) where
     recover ma = stateT $ \s -> recover (runStateT ma s)
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

splitStream :: Stream s -> Maybe (s, Stream s)
splitStream = nested wrapped List.uncons


-- === Instances === --

type instance Token (StateT (Stream s) m) = s
instance Monad m => MonadTokenParser (StateT (Stream s) m) where
    lookupToken = modify @Stream go where
        go s = case splitStream s of
            Nothing     -> (Nothing, s)
            Just (t,s') -> (Just t, s')



-------------------------------------
-- === ProgressTrackingParserT === --
-------------------------------------

-- === Definition === --

newtype ProgressTrackingParserT e m a = ProgressTrackingParserT (StateT Progress m (Either e a)) deriving (Functor)
makeLenses ''ProgressTrackingParserT


-- === Running === --

runProgressTrackingParserT :: forall e m a. Monad m => ProgressTrackingParserT e m a -> m (Either e a)
runProgressTrackingParserT = fmap fst . flip runStateT (Progress False) . unwrap


-- === Primary instances === --

instance Monad m => Applicative (ProgressTrackingParserT e m) where
    pure    = wrap . pure . Right
    f <*> a = wrap $ liftA2 (<*>) (unwrap f) (unwrap a)

instance Monad m => Monad (ProgressTrackingParserT e m) where
    a >>= f = wrap $ unwrap a >>= withRightM (unwrap . f)

instance MonadIO m => MonadIO (ProgressTrackingParserT e m) where
    liftIO = wrap . liftIO . fmap Right

instance (Monad m, IsString e) => MonadPlus   (ProgressTrackingParserT e m)
instance (Monad m, IsString e) => Alternative (ProgressTrackingParserT e m) where
    empty = throw "Unknown error"
    l <|> r = wrap $ do
        put @Progress $ Progress False
        la <- unwrap l
        p  <- unwrap <$> get @Progress
        if p || isRight la then return la else unwrap r


-- === Parser instances === --

type instance Error (ProgressTrackingParserT e m) = e

instance Monad m => MonadProgressParser (ProgressTrackingParserT e m) where
    getProgress   = wrap $ Right <$> get @Progress
    putProgress p = wrap $ Right <$> put @Progress p
    try m = wrap $ do
        a <- unwrap m
        when (isLeft a) $ put @Progress (Progress False)
        return a

instance Monad m => MonadRecoveryParser (ProgressTrackingParserT e m) where
    recover = wrapped %~ fmap Right

instance Monad m => MonadThrowParser (ProgressTrackingParserT e m) where
    throw = wrap . return . Left




-------------------------------
-- tests

instance (Monad m, Show t) => MonadErrorBuilder t m String where
    buildError t = return $ "ERROR: " <> show t


runTest :: (MonadIO m, MonadPlus m) => m (Either String [Char])
runTest = runProgressTrackingParserT @String
        $ flip evalStateT (Stream "babbbaabab" :: Stream Char)
        $ flip evalStateT (mempty :: Offset)
        $ (many (token 'a' <|> token 'b') <* token 'x')

main :: IO ()
main = do
    print =<< runTest
    print "---"

--
-- --
-- --
-- -- main :: IO ()
-- -- main = do
-- --     print "hello"
