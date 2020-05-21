{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor.Foldable.Monadic
  ( -- * Folding
    cataM
  , preproM
  , paraM
  , zygoM
  , histoM, histoM'
  , dynaM, dynaM', dynaM''

    -- * Unfolding
  , anaM
  , postproM
  , apoM
  , cozygoM
  , futuM, futuM'
  , codynaM, codynaM', codynaM''

    -- * Refolding
  , hyloM, metaM
  , hyloM', metaM'
  , chronoM, cochronoM
  , chronoM' -- cochronoM'

    -- * Generalized Folding
  , gcataM

    -- * Others
  , mutuM, comutuM
  , mutuM', comutuM'
  , cascadeM, iterateM
  ) where

import           Control.Comonad              (Comonad (..))
import           Control.Comonad.Cofree       (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as CF (CofreeF (..))
import           Control.Monad                ((<=<), liftM, liftM2)
import           Control.Monad.Free           (Free (..))
import qualified Control.Monad.Trans.Free     as FR (FreeF (..))
import           Data.Functor.Foldable        (Recursive (..), Corecursive (..), Base)

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
  where h = return . embed <=< mapM h <=< psi

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
  where h = return . embed <=< mapM (either return h) <=< psi

-- | histomorphism on anamorphism variant
histoM :: (Monad m, Traversable (Base t), Recursive t)
       => (Base t (Cofree (Base t) a) -> m a) -- ^ algebra
       -> t -> m a
histoM phi = h
  where h = phi <=< mapM f . project
        f = anaM (liftM2 (CF.:<) <$> h <*> return . project)

-- | histomorphism on catamorphism variant
histoM' :: (Monad m, Traversable (Base t), Recursive t)
        => (Base t (Cofree (Base t) a) -> m a) -- ^ algebra
        -> t -> m a
histoM' phi = return . extract <=< cataM f
  where f = liftM2 (:<) <$> phi <*> return

-- | futumorphism on catamorphism variant
futuM :: (Monad m, Traversable (Base t), Corecursive t)
      => (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
      -> a -> m t
futuM psi = h
  where h = return . embed <=< mapM f <=< psi
        f = cataM $ \case
          FR.Pure  a -> h a
          FR.Free fb -> return (embed fb)

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

-- | hylomorphism on combination variant of ana to cata
hyloM' :: forall m t a b. (Monad m, Traversable (Base t), Recursive t, Corecursive t)
       => (Base t b -> m b)   -- ^ algebra
       -> (a -> m (Base t a)) -- ^ coalgebra
       -> a -> m b
hyloM' phi psi = (cataM phi :: t -> m b) <=< (anaM psi :: a -> m t)

-- | metamorphism on recursive variant
metaM :: (Monad m, Traversable (Base t), Recursive s, Corecursive t, Base s ~ Base t)
      => (Base t t -> m t)   -- ^ algebra
      -> (s -> m (Base s s)) -- ^ coalgebra
      -> s -> m t
metaM _phi _psi = h
  where h = return . embed <=< mapM h . project

-- | metamorphism on combination variant of cata to ana
metaM' :: (Monad m, Corecursive c, Traversable (Base c), Traversable (Base t), Recursive t)
       => (Base t a -> m a)   -- ^ algebra
       -> (a -> m (Base c a)) -- ^ coalgebra
       -> t -> m c
metaM' phi psi = anaM psi <=< cataM phi

-- | chronomorphism on recursive variant over hylomorphism
chronoM' :: (Monad m, Traversable t)
         => (t (Cofree t b) -> m b) -- ^ algebra
         -> (a -> m (t (Free t a))) -- ^ coalgebra
         -> a -> m b
chronoM' phi psi = return . extract <=< hyloM f g . Pure
  where f = liftM2 (:<) <$> phi <*> return
        g (Pure  a) = psi a
        g (Free fb) = return fb

-- | chronomorphism on combination variant of futu to hist
chronoM :: forall m t a b. (Monad m, Traversable (Base t), Recursive t, Corecursive t)
        => (Base t (Cofree (Base t) b) -> m b) -- ^ algebra
        -> (a -> m (Base t (Free (Base t) a))) -- ^ coalgebra
        -> a -> m b
chronoM phi psi = (histoM phi :: t -> m b) <=< (futuM psi :: a -> m t)

-- | cochronomorphism on combination variant of histo to futu
cochronoM :: (Monad m, Corecursive c, Traversable (Base c), Traversable (Base t), Recursive t)
          => (Base t (Cofree (Base t) a) -> m a) -- ^ algebra
          -> (a -> m (Base c (Free (Base c) a))) -- ^ coalgebra
          -> t -> m c
cochronoM phi psi = futuM psi <=< histoM phi

-- | dynamorphism on recursive variant over chronomorphism
dynaM :: (Monad m, Traversable (Base t), Recursive t, Corecursive t)
      => (Base t (Cofree (Base t) b) -> m b) -- ^ algebra
      -> (a -> m (Base t a))                 -- ^ coalgebra
      -> a -> m b
dynaM phi psi = chronoM' phi (return . fmap Pure <=< psi)

-- | dynamorphism on combination variant of ana to histo
dynaM' :: forall m t a c. (Monad m, Traversable (Base t), Recursive t, Corecursive t)
       => (Base t (Cofree (Base t) c) -> m c) -- ^ algebra
       -> (a -> m (Base t a))                 -- ^ coalgebra
       -> a -> m c
dynaM' phi psi = (histoM phi :: t -> m c) <=< (anaM psi :: a -> m t)

-- | dynamorphism on recursive variant over hylomorphism
dynaM'' :: (Monad m, Traversable t)
        => (t (Cofree t c) -> m c) -- ^ algebra
        -> (a -> m (t a))          -- ^ coalgebra
        -> a -> m c
dynaM'' phi psi = return . extract <=< hyloM f psi
  where f = liftM2 (:<) <$> phi <*> return

-- | codynamorphism on recursive variant over chronomorphism
codynaM :: (Monad m, Traversable t)
        => (t b -> m b)            -- ^ algebra
        -> (a -> m (t (Free t a))) -- ^ coalgebra
        -> a -> m b
codynaM phi psi = chronoM' (phi . fmap extract) psi

-- | codynamorphism on combination variant of histo to ana
codynaM' :: (Monad m, Corecursive c, Traversable (Base c), Traversable (Base t), Recursive t)
         => (Base t (Cofree (Base t) a) -> m a) -- ^ algebra
         -> (a -> m (Base c a))                 -- ^ coalgebra
         -> t -> m c
codynaM' phi psi = anaM psi <=< histoM phi

-- | codynamorphism on recursive variant over hylomorphism
codynaM'' :: (Monad m, Traversable t)
          => (t b -> m b)            -- ^ algebra
          -> (a -> m (t (Free t a))) -- ^ coalgebra
          -> a -> m b
codynaM'' phi psi = hyloM phi g . Pure
  where g (Pure  a) = psi a
        g (Free fb) = return fb

-- | mutumorphism on mutual recursive
mutuM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t (a, b) -> m b) -- ^ algebra
      -> (Base t (a, b) -> m a) -- ^ algebra
      -> t -> m b
mutuM q p = v q p
  where u f g = f <=< mapM (liftM2 (,) <$> u f g <*> v g f) . project
        v g f = g <=< mapM (liftM2 (,) <$> u f g <*> v g f) . project

-- | mutumorphism on recursive variant over catamorphism
mutuM' :: (Monad m, Traversable (Base t), Recursive t)
       => (a -> b)          -- ^ project
       -> (Base t a -> m a) -- ^ algebra
       -> t -> m b
mutuM' f phi = return . f <=< cataM phi

-- | comutumorphism on comutual recursive
comutuM :: (Monad m, Traversable (Base t), Corecursive t)
        => (b -> m (Base t (Either a b))) -- ^ coalgebra
        -> (a -> m (Base t (Either a b))) -- ^ coalgebra
        -> b -> m t
comutuM q p = v q p
  where u f g = fmap embed . mapM (either (u f g) (v g f)) <=< f
        v g f = fmap embed . mapM (either (u f g) (v g f)) <=< g

-- | comutumorphism on recursive variant over anamorphism
comutuM' :: (Monad m, Traversable (Base t), Corecursive t)
         => (b -> a)            -- ^ embed
         -> (a -> m (Base t a)) -- ^ coalgebra
         -> b -> m t
comutuM' f psi = anaM psi . f

-- | prepromorphism
preproM :: (Monad m, Traversable (Base t), Recursive t, Corecursive t)
        => (Base t t -> m (Base t t)) -- ^ monadic natural transformation
        -> (Base t a -> m a)          -- ^ algebra
        -> t -> m a
preproM h phi = u
  where u = phi <=< mapM f . project
        f = u <=< cataM (return . embed <=< h)

-- | postpromorphism
postproM :: (Monad m, Traversable (Base t), Recursive t, Corecursive t)
         => (Base t t -> m (Base t t)) -- ^ monadic natural transformation
         -> (a -> m (Base t a))        -- ^ coalgebra
         -> a -> m t
postproM h psi = u
  where u = return . embed <=< mapM f <=< psi
        f = anaM (h . project) <=< u

-- | cascade (a.k.a supermap)
cascadeM :: (Monad m, Corecursive (f a), Traversable (Base (f a)), Traversable f, Recursive (f a))
         => (a -> m a) -- ^ pre-operator
         -> f a -> m (f a)
cascadeM f = u
  where u = return . embed <=< mapM u <=< mapM (mapM f) . project

-- | iterate
iterateM :: (Monad m, Corecursive (f a), Traversable (Base (f a)), Traversable f, Recursive (f a))
         => (a -> m a) -- ^ post-operator
         -> f a -> m (f a)
iterateM f = u
  where u = return . embed <=< mapM (mapM f) <=< mapM u . project


-- | generalized catamorphism
gcataM :: (Monad m, Comonad w, Traversable w, Traversable (Base t), Recursive t, b ~ w a)
       => (Base t (w b) -> m (w (Base t b))) -- ^ Distributive (Base t) w b
       -> (Base t (w a) -> m a)              -- ^ algebra
       -> t -> m a
gcataM k g = liftM extract . cataM phi
  where phi = mapM g <=< k <=< return . fmap duplicate
