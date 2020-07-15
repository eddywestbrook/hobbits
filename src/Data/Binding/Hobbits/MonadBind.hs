{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Binding.Hobbits.MonadBind (MonadBind(..), MonadStrongBind(..)) where

import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.Liftable (mbLift)
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.QQ

import Data.Type.RList

import Control.Monad.Identity (Identity(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT(..), get, lift, put, runStateT)

class Monad m => MonadBind m where
  mbM :: NuMatching a => Mb ctx (m a) -> m (Mb ctx a)

nuM :: (MonadBind m, NuMatching b) => (Name a -> m b) -> m (Binding a b)
nuM = mbM . nu

instance MonadBind Identity where
  mbM = Identity . fmap runIdentity

instance MonadBind Maybe where
  mbM [nuP| Just x |] = return x
  mbM [nuP| Nothing |] = Nothing

instance MonadBind m => MonadBind (ReaderT r m) where
  mbM mb = ReaderT $ \r -> mbM $ fmap (flip runReaderT r) mb

-- | A version of 'MonadBind' that does not require a 'NuMatching' instance on
-- the element type of the multi-binding in the monad
class MonadBind m => MonadStrongBind m where
  strongMbM :: Mb ctx (m a) -> m (Mb ctx a)

instance MonadStrongBind Identity where
  strongMbM = Identity . fmap runIdentity

instance MonadStrongBind m => MonadStrongBind (ReaderT r m) where
  strongMbM mb = ReaderT $ \r -> strongMbM $ fmap (flip runReaderT r) mb

-- | State types that can incorporate name-bindings
class NuMatching s => BindState s where
  bindState :: Mb ctx s -> s

instance BindState (Closed s) where
  bindState = mbLift

instance (MonadBind m, BindState s) => MonadBind (StateT s m) where
  mbM mb_m = StateT $ \s ->
    mbM (fmap (\m -> runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

instance (MonadStrongBind m, BindState s) => MonadStrongBind (StateT s m) where
  strongMbM mb_m = StateT $ \s ->
    strongMbM (fmap (\m -> runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))


-- | A monad whose effects are closed
class Monad m => MonadClosed m where
  closedM :: Closed (m a) -> m (Closed a)

instance MonadClosed Identity where
  closedM = Identity . clApply $(mkClosed [| runIdentity |])

instance (MonadClosed m, Closable s) => MonadClosed (StateT s m) where
  closedM clm =
    do s <- get
       cl_a_s <- lift $ closedM ($(mkClosed [| runStateT |]) `clApply` clm
                                 `clApply` toClosed s)
       put (snd $ unClosed cl_a_s)
       return ($(mkClosed [| fst |]) `clApply` cl_a_s)
