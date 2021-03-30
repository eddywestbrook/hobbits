{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Data.Binding.Hobbits.MonadBind
-- Copyright   : (c) 2020 Edwin Westbrook
--
-- License     : BSD3
--
-- Maintainer  : westbrook@galois.com
-- Stability   : experimental
-- Portability : GHC
--
-- This module defines monads that are compatible with the notion of
-- name-binding, where a monad is compatible with name-binding iff it can
-- intuitively run computations that are inside name-bindings. More formally, a
-- /binding monad/ is a monad with an operation 'mbM' that commutes name-binding
-- with the monadic operations, meaning:
--
-- > 'mbM' ('nuMulti' $ \ns -> 'return' a) == 'return' ('nuMulti' $ \ns -> a)
-- > 'mbM' ('nuMulti' $ \ns -> m >>= f)
-- >   == 'mbM' ('nuMulti' $ \ns -> m) >>= \mb_x ->
-- >      'mbM' (('nuMulti' $ \ns x -> f x) `'mbApply'` mb_x)

module Data.Binding.Hobbits.MonadBind (MonadBind(..), MonadStrongBind(..)) where

import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.Liftable (Liftable(..), mbMaybe)
import Data.Binding.Hobbits.Mb
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.QQ

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Reader (ReaderT(..))
import qualified Control.Monad.State.Lazy as Lazy
import qualified Control.Monad.State.Strict as Strict

-- | The class of name-binding monads
class Monad m => MonadBind m where
  mbM :: NuMatching a => Mb ctx (m a) -> m (Mb ctx a)

-- | Bind a name inside a computation and return the name-binding whose body was
-- returned by the computation
nuM :: (MonadBind m, NuMatching b) => (Name a -> m b) -> m (Binding a b)
nuM = mbM . nu

instance MonadBind Identity where
  mbM = Identity . fmap runIdentity

instance MonadBind Maybe where
  mbM = mbMaybe

instance MonadBind m => MonadBind (MaybeT m) where
  mbM = MaybeT . fmap mbM . mbM . fmap runMaybeT

instance Liftable e => MonadBind (Either e) where
  mbM [nuP| Right mb_a |] = Right mb_a
  mbM [nuP| Left mb_e |] = Left $ mbLift mb_e

instance (MonadBind m, Liftable e) => MonadBind (ExceptT e m) where
  mbM = ExceptT . fmap mbM . mbM . fmap runExceptT

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

instance (MonadBind m, BindState s) => MonadBind (Lazy.StateT s m) where
  mbM mb_m = Lazy.StateT $ \s ->
    mbM (fmap (\m -> Lazy.runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

instance (MonadStrongBind m, BindState s) => MonadStrongBind (Lazy.StateT s m) where
  strongMbM mb_m = Lazy.StateT $ \s ->
    strongMbM (fmap (\m -> Lazy.runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

instance (MonadBind m, BindState s) => MonadBind (Strict.StateT s m) where
  mbM mb_m = Strict.StateT $ \s ->
    mbM (fmap (\m -> Strict.runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

instance (MonadStrongBind m, BindState s) => MonadStrongBind (Strict.StateT s m) where
  strongMbM mb_m = Strict.StateT $ \s ->
    strongMbM (fmap (\m -> Strict.runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))


-- | A monad whose effects are closed
class Monad m => MonadClosed m where
  closedM :: Closed (m a) -> m (Closed a)

instance MonadClosed Identity where
  closedM = Identity . clApply $(mkClosed [| runIdentity |])

instance (MonadClosed m, Closable s) => MonadClosed (Lazy.StateT s m) where
  closedM clm =
    do s <- Lazy.get
       cl_a_s <- lift $ closedM ($(mkClosed [| Lazy.runStateT |]) `clApply` clm
                                 `clApply` toClosed s)
       Lazy.put (snd $ unClosed cl_a_s)
       return ($(mkClosed [| fst |]) `clApply` cl_a_s)

instance (MonadClosed m, Closable s) => MonadClosed (Strict.StateT s m) where
  closedM clm =
    do s <- Strict.get
       cl_a_s <- lift $ closedM ($(mkClosed [| Strict.runStateT |]) `clApply` clm
                                 `clApply` toClosed s)
       Strict.put (snd $ unClosed cl_a_s)
       return ($(mkClosed [| fst |]) `clApply` cl_a_s)
