{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor.Foldable.Monadic
  ( cataM, anaM
  , paraM, apoM
  , histoM, futuM
  , histoM', futuM'
  , zygoM, cozygoM
  , hyloM, metaM
  , chronoM, cochronoM
  , chronoM', cochronoM'
  ) where

import           Control.Comonad              (Comonad (..))
import           Control.Comonad.Cofree       (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as Cf (CofreeF (..))
import           Control.Monad                ((<=<), liftM2)
import           Control.Monad.Free           (Free (..))
import qualified Control.Monad.Trans.Free     as Fr (FreeF (..))
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

-- | histomorphism on anamorphism variant
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
  where f = liftM2 (:<) <$> phi <*> return

-- | futumorphism on catamorphism variant
futuM :: (Monad m, Traversable (Base t), Corecursive t)
      => (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
      -> a -> m t
futuM psi = h
  where h = (return . embed) <=< mapM f <=< psi
        f = cataM $ \case
          Fr.Pure  a -> h a
          Fr.Free fb -> return (embed fb)

-- | futumorphism on anamorphism variant
futuM' :: (Monad m, Traversable (Base t), Corecursive t)
       => (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
       -> a -> m t
futuM' psi = anaM f . Pure
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

-- | hylomorphism on recursive variant
hyloM :: (Monad m, Traversable t)
      => (t b -> m b)   -- ^ algebra
      -> (a -> m (t a)) -- ^ coalgebra
      -> a -> m b
hyloM phi psi = h
  where h = phi <=< mapM h <=< psi

-- FIXME: I couldn't compile with this type signature.
-- | hylomorphism on combination variant of ana to cata
-- hyloM' :: (Monad m, Traversable (Base t), Recursive t, Corecursive t)
--        => (Base t b -> m b)   -- ^ algebra
--        -> (a -> m (Base t a)) -- ^ coalgebra
--        -> a -> m b
hyloM' phi psi = cataM phi <=< anaM psi

-- | metamorphism on recursive variant
metaM :: (Monad m, Traversable (Base t), Recursive s, Corecursive t, Base s ~ Base t)
      => (Base t t -> m t)
      -> (s -> m (Base s s))
      -> s -> m t
metaM phi psi = h
  where h = (return . embed) <=< mapM h . project

-- | metamorphism on combination variant of cata to ana
metaM' :: (Monad m, Corecursive c, Traversable (Base c), Traversable (Base t), Recursive t)
       => (Base t a -> m a)   -- ^ algebra
       -> (a -> m (Base c a)) -- ^ coalgebra
       -> t -> m c
metaM' phi psi = anaM psi <=< cataM phi

-- | chronomorphism on recursive variant over hylomorphism
chronoM :: (Monad m, Traversable t)
        => (t (Cofree t b) -> m b) -- ^ algebra
        -> (a -> m (t (Free t a))) -- ^ coalgebra
        -> a -> m b
chronoM phi psi = return . extract <=< hyloM f g . Pure
  where f = liftM2 (:<) <$> phi <*> return
        g (Pure  a) = psi a
        g (Free fb) = return fb

-- FIXME: I couldn't compile with this type signature.
-- | chronomorphism on combination variant of futu to hist
-- chronoM' :: (Monad m, Traversable (Base t), Recursive t, Corecursive t)
--          => (Base t (Cofree (Base t) c) -> m c) -- ^ algebra
--          -> (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
--          -> a -> m c
chronoM' phi psi = histoM phi <=< futuM psi

cochronoM = undefined

cochronoM' :: (Monad m, Corecursive c, Traversable (Base c), Traversable (Base t), Recursive t)
           => (Base t (Cofree (Base t) a) -> m a)
           -> (a -> m (Base c (Free (Base c) a)))
           -> t -> m c
cochronoM' phi psi = futuM psi <=< histoM phi
