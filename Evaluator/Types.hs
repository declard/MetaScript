{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}

module MetaScript.Evaluator.Types (
  Object(..),
  Primitive(..),
  Fields(..),
  Function(..),
  Map(..),
  Arguments(..),
  Context(..),
  IMacro(..),
  Evaluation(..),
  runEvaluation,
  newRef,
  readRef,
  writeRef,
  modifyRef,
  withRef,
  takeRef,
  tryTakeRef,
  putRef,
  newId
) where

import qualified MetaScript.Parser as P
import Data.Monoid
import qualified Data.Map.Strict as DM
import Data.Functor.Identity
import Data.Text(Text)
import Control.Concurrent.MVar
import Control.Monad.State as S
import Control.Monad.Reader as R
import Data.Int
import Control.Applicative


newtype Evaluation a = Evaluation { evaluation :: ReaderT (MVar Int64) (StateT Context IO) a } deriving(Functor, Applicative, Monad, MonadIO, MonadFix)

type ImplicitContext = DM.Map Text Object
type ExplicitContext = DM.Map Text (MVar Object)
data Context = Context { implicit :: ImplicitContext, explicit :: ExplicitContext }

type Map = DM.Map Primitive Object
data Fields = Fields { readOnly :: Bool, objectId :: Int64, fields :: (MVar (DM.Map Primitive Object)) }
data Object =   Object Fields
              | Function Fields Function
              | Array Fields (MVar (DM.Map Integer Object))
              | Primitive Fields Primitive
data Primitive =  Number Integer
                | String Text
                | Bool Bool
                | Unique Text deriving(Eq, Ord, Show)
data Function =   ImbeddedFunction ([Object] -> Evaluation Object)
                | ImbeddedMacro (Maybe Object -> [P.Expression] -> Evaluation Object)
                | ConstructedFunction Context Arguments P.Expression
data Arguments = Variadic Text | Fixed [Text] deriving(Eq, Ord, Show)

type IMacro = (Maybe Object) -> [P.Expression] -> Evaluation Object

instance MonadState Context Evaluation where
  get = Evaluation $ lift get
  put v = Evaluation $ lift $ put v

newId = Evaluation $ do
  v <- ask
  liftIO $ modifyMVar v (\v -> return (v + 1, v))
  
runEvaluation e context = do
  firstObjectId <- newMVar 0
  evalStateT (runReaderT (evaluation e) firstObjectId) context
  
cde = error "Cyclic dependency detected"

newRef :: (MonadIO m) => a -> m (MVar a)
newRef = liftIO . newMVar

readRef :: (MonadIO m) => MVar a -> m a
readRef r = liftIO $ do
  v <- tryReadMVar r
  maybe cde return v

writeRef :: MVar a -> a -> Evaluation ()
writeRef r v = modifyRef r (const v)

takeRef r = liftIO $ do
  v <- tryTakeMVar r
  maybe cde return v
  
tryTakeRef r = liftIO $ tryTakeMVar r
  
putRef r v = liftIO $ putMVar r v

modifyRef :: MVar a -> (a -> a) -> Evaluation ()
modifyRef r m = liftIO $ do
  v <- tryTakeMVar r
  maybe cde (putMVar r . m) v

withRef :: MVar a -> (a -> Evaluation b) -> Evaluation b  
withRef r c = do
  v <- liftIO $ tryTakeMVar r
  let execute v = do
        result <- c v
        liftIO $ putMVar r v
        return result
  maybe cde execute v
  