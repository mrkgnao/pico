{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Edible.Prelude
  ( module X
  , (>>>)
  , RecursionDepthM
  , HasRecursionDepth(..)
  , recur
  , tshow
  , LogItem(..)
  , Message
  , logText
  ) where

import           Control.Applicative         as X
import           Control.Monad               as X
import           Data.Foldable               as X
import           Data.Semigroup              as X
import           Data.Traversable            as X

import           Control.Monad.Identity      as X (Identity (..))

-- Data structures
import           Data.List.NonEmpty          as X (NonEmpty (..))
import           Data.Map                    as X (Map)
import           Data.Text                   as X (Text)

-- Monad transformers
import           Control.Monad.Except        as X (Except, ExceptT,
                                                   MonadError (..), runExcept,
                                                   runExceptT)
import           Control.Monad.Reader        as X (MonadReader (..), Reader,
                                                   ReaderT, runReader,
                                                   runReaderT)
import           Control.Monad.RWS.Strict    as X (MonadRWS (..), RWS, RWST,
                                                   runRWS, runRWST)
import           Control.Monad.State         as X (MonadState (..), State,
                                                   StateT, modify, runState,
                                                   runStateT)
import           Control.Monad.Writer.Strict as X (MonadWriter (..), Writer,
                                                   WriterT, runWriter,
                                                   runWriterT)

import qualified Control.Category
import           Control.Lens                as X
import qualified Data.Text                   as Text

import           Data.Typeable               as X (Typeable)
import           GHC.Generics                as X (Generic)

(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) = (Control.Category.>>>)

type RecursionDepthM env m = (HasRecursionDepth env, MonadReader env m)

class HasRecursionDepth env where
  recursionDepth :: Lens' env Int

recur :: RecursionDepthM env m => m a -> m a
recur = local (recursionDepth +~ 1)

tshow :: Show a => a -> Text
tshow = Text.pack . show

data LogItem = LogItem { _messageDepth :: !Int, _messageContents :: Message }

instance Show LogItem where
  show (LogItem d (MsgText m)) = show d ++ ": " ++ Text.unpack m
  -- show (LogItem d m) = show d ++ ": " ++ show m

newtype Message = MsgText Text
  deriving Show

logText :: (MonadWriter [LogItem] m, RecursionDepthM env m) => Text -> m ()
logText t = do
  depth <- view recursionDepth
  tell [LogItem depth (MsgText t)]

