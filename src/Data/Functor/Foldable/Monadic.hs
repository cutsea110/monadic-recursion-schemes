{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Functor.Foldable.Monadic
  ( cataM, anaM
  , paraM, apoM
  , histoM, futuM
  , zygoM, cozygoM
  , hyloM
  ) where

import           Control.Comonad              (Comonad (..))
import           Control.Comonad.Cofree       (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as Cf (CofreeF (..))
import           Control.Monad                ((<=<), liftM2)
import           Control.Monad.Free           (Free (..))
import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.Reader   (ReaderT, ask, runReaderT)
import           Data.Functor.Foldable        (Recursive (..), Corecursive (..), Base, Fix (..))


-- | catamorphism
cataM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t a -> m a) -- ^ algebra
      -> t -> m a
cataM phi = h
  where h = phi <=< mapM h . project

-- | anamorphism
anaM :: (Monad m, Traversable (Base t), Corecursive t)
     => (a -> m (Base t a)) -- ^ coalgebra
     -> a -> m t
anaM psi = h
  where h = (return . embed) <=< mapM h <=< psi

-- | paramorphism
paraM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t (t, a) -> m a) -- ^ algebra
      -> t -> m a
paraM phi = h
  where h = phi <=< mapM (liftM2 (,) <$> return <*> h) . project

-- | apomorphism
apoM :: (Monad m, Traversable (Base t), Corecursive t)
     => (a -> m (Base t (Either t a))) -- ^ coalgebra
     -> a -> m t
apoM psi = h
  where h = (return . embed) <=< mapM (either return h) <=< psi

-- | histomorphism on recursion variant
histoM :: (Monad m, Traversable (Base t), Recursive t)
       => (Base t (Cofree (Base t) a) -> m a) -- ^ algebra
       -> t -> m a
histoM phi = h
  where h = phi <=< mapM f . project
        f = anaM (liftM2 (Cf.:<) <$> h <*> (return . project))

-- | histomorphism on catamorphism variant
histoM' :: (Monad m, Traversable (Base t), Recursive t)
        => (Base t (Cofree (Base t) a) -> m a)
        -> t -> m a
histoM' phi = return . extract <=< cataM f
  where f  = return . uncurry (:<) <=< (liftM2 (,) <$> phi <*> return)

-- | futumorphism on anamorphism variant
futuM :: (Monad m, Traversable (Base t), Corecursive t)
      => (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
      -> a -> m t
futuM psi = anaM f . Pure
  where f (Pure  a) = psi a
        f (Free fb) = return fb

-- | zygomorphism
zygoM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t a -> m a)      -- ^ algebra for fst
      -> (Base t (a, b) -> m b) -- ^ algebra for snd from product
      -> t -> m b
zygoM f phi = return . snd <=< cataM g
  where g = liftM2 (,) <$> (f <=< return . fmap fst) <*> phi

-- | cozygomorphism
cozygoM :: (Monad m, Traversable (Base t), Corecursive t)
        => (a -> m (Base t a))            -- ^ coalgebra for fst
        -> (b -> m (Base t (Either a b))) -- ^ coalgebra for snd to coproduct
        -> b -> m t
cozygoM f psi = anaM g . Right
  where g = either (return . fmap Left <=< f) psi

-- | hylomorphism
hyloM :: (Monad m, Traversable t)
      => (t b -> m b)   -- ^ algebra
      -> (a -> m (t a)) -- ^ coalgebra
      -> a -> m b
hyloM phi psi = h
  where h = phi <=< mapM h <=< psi
