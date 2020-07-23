{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear algebra after Fortran

module LinAlg1 where

import Data.Kind
-- import Control.Category

infixl 7 :*
infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

data L :: Type -> Type -> Type where
  Scale :: Num a => a -> L a a  -- TODO: Semiring instead of Num
  ForkL :: L u v -> L u v' -> L u (v :* v')
  JoinL :: L u v -> L u' v -> L (u :* u') v

pattern Fork :: L u v -> L u v' -> L u (v :* v')
pattern Fork f g <- (unforkL -> (f,g))
 where Fork = ForkL

pattern Join :: L u v -> L u' v -> L (u :* u') v
pattern Join f g <- (unjoinL -> (f,g))
 where Join = JoinL

#if 0

-- Note: Num in Join is for the semantics, not the implementation.

-- For linear functions.
forkF :: (u -> v) -> (u -> v') -> (u -> v :* v')
forkF f g u = (f u, g u)

-- For linear functions. TODO: generalize from Num
joinF :: Num v => (u -> v) -> (u' -> v) -> (u :* u' -> v)
joinF f g (u,u') = f u + g u'

exlF :: u :* v -> u
exlF = fst

exrF :: u :* v -> v
exrF = snd

unforkF :: (u -> v :* v') -> (u -> v) :* (u -> v')
unforkF h = (exlF . h, exrF . h)

inlF :: Num v => u -> u :* v
inlF u = (u,0)

inrF :: Num u => v -> u :* v
inrF v = (0,v)

unjoinF :: (Num u, Num u') => (u :* u' -> v) -> (u -> v) :* (u' -> v)
unjoinF h = (h . inlF, h . inrF)

-- Denotation
mu :: L u v -> (u -> v)
mu (Scale a) = (a *)
mu (ForkL f g) = forkF (mu f,mu g)
mu (JoinL f g) = joinF (mu f,mu g)  -- needs a Num

#endif

-- forkL :: L u v -> L u v' -> L u (v :* v')
-- forkL = ForkL

-- joinL :: L u v -> L u' v -> L (u :* u') v
-- joinL = JoinL

unforkL :: L u (v :* v') -> L u v :* L u v'
unforkL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unforkL (ForkL f g) = (f,g)
unforkL (JoinL f g) = (JoinL p r, JoinL q s)
 where
  (p,q) = unforkL f
  (r,s) = unforkL g

-- unforkL (Join (f,g)) = (joinL *** joinL) (transpose (unforkL f, unforkL g))

-- transpose :: (a :* b) :* (c :* d) -> (a :* c) :* (b :* d)
-- transpose ((a,b),(c,d)) = ((a,c),(b,d))

-- Join (f,g) :: L (u * u') (v :* v')
-- f :: L u  (v :* v')
-- g :: L u' (v * v')
-- p :: L u v
-- q :: L u v'
-- r :: L u' v
-- s :: L u' v'

unjoinL :: L (u :* u') v -> L u v :* L u' v
unjoinL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unjoinL (JoinL f g) = (f,g)
unjoinL (ForkL f g) = (ForkL p r, ForkL q s)
 where
  (p,q) = unjoinL f
  (r,s) = unjoinL g

-- TODO: use pattern synonyms in place of unforkL and unjoinL
