{-# LANGUAGE UndecidableInstances #-} -- see below

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Isomorphisms

module Category.Isomorphism where

import Prelude hiding (id,(.))

import Misc
import Category

infix 0 :<->
data Iso k a b = (:<->) { isoFwd :: a `k` b, isoRev :: b `k` a }

inv :: Iso k a b -> Iso k b a
inv (f :<-> f') = f' :<-> f
{-# INLINE inv #-}

-- | Form an ivolution from a _self-inverse_ arrow.
involution :: (a `k` a) -> Iso k a a
involution f = f :<-> f

infix 0 <->
type (<->) = Iso (->)

instance Category k => Category (Iso k) where
  type Obj' (Iso k) = Obj k
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')
  {- INLINE id #-}
  {- INLINE (.) #-}

#if 0
instance AssociativePCat k => AssociativePCat (Iso k) where
  lassocP = lassocP :<-> rassocP
  rassocP = rassocP :<-> lassocP
  {- INLINE lassocP #-}
  {- INLINE rassocP #-}

instance BraidedPCat k => BraidedPCat (Iso k) where
  swapP = swapP :<-> swapP
  {-# INLINE swapP #-}
#endif

instance Monoidal k p => Monoidal (Iso k) p where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')
  {- INLINE (***) #-}

#if 0
instance AssociativeSCat k => AssociativeSCat (Iso k) where
  lassocS = lassocS :<-> rassocS
  rassocS = rassocS :<-> lassocS
  {- INLINE lassocS #-}
  {- INLINE rassocS #-}
#endif

instance Comonoidal k co => Comonoidal (Iso k) co where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')
  {- INLINE (+++) #-}

#if 0
instance BraidedSCat k => BraidedSCat (Iso k) where
  swapS = swapS :<-> swapS
  {-# INLINE swapS #-}

instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
  {-# INLINE lunit #-}
  {-# INLINE runit #-}
  {-# INLINE lcounit #-}
  {-# INLINE rcounit #-}
#endif

-- | Apply one isomorphism via another
via :: (Category k, Obj2 k a b) => Iso k b b -> Iso k a b -> Iso k a a
(g :<-> g') `via` (ab :<-> ba) = ba . g . ab :<-> ba . g' . ab
{-# INLINE via #-}

join2Iso :: (Cocartesian k co, Obj3 k a c d) 
         => (c `k` a) :* (d `k` a) <-> ((c `co` d) `k` a)
join2Iso = join2 :<-> unjoin2

fork2Iso :: (Cartesian k p, Obj3 k a c d)
         => (a `k` c) :* (a `k` d) <-> (a `k` (c `p` d))
fork2Iso = fork2 :<-> unfork2

joinIso :: (CocartesianR k r co, Obj2 k a b) => r (a `k` b) <-> co r a `k` b
joinIso = join :<-> unjoin

forkIso :: (CartesianR k r p, Obj2 k a b) => r (a `k` b) <-> (a `k` p r b)
forkIso = fork :<-> unfork

-- curryIso :: (Closed k, Obj3 k a b c)
--          => ((a :* b) `k` c) <-> (a `k` (b -> c))
-- curryIso = curry :<-> uncurry



-- Illegal instance declaration for ‘Monoidal (Iso k) p’
--   The coverage condition fails in class ‘Monoidal’
--     for functional dependency: ‘k -> p’
--   Reason: lhs type ‘Iso k’ does not determine rhs type ‘p’
--   Un-determined variable: p
--   Using UndecidableInstances might help
