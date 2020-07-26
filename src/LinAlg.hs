-- | Linear algebra after Fortran

module LinAlg where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip)

import GHC.Generics (Par1(..), (:*:)(..), (:.:)(..))
import qualified Control.Arrow as A
import Data.Distributive
import Data.Functor.Rep

infixl 7 :*
type (:*)  = (,)

-- infixl 6 :+
-- type (:+)  = Either

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

type V f = (Representable f, Foldable f, Eq (Rep f))
type V2 f g = (V f, V g)
type V3 f g h = (V2 f g, V h)

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

sum :: (Foldable f, Additive a) => f a -> a
sum = foldr (+) zero

-- | Vector addition
infixl 6 +^
(+^) :: (Representable f, Additive s) => f s -> f s -> f s
(+^) = liftR2 (+)

instance Additive Double where { zero = 0; (+) = (P.+) }
instance Semiring Double where { one  = 1; (*) = (P.*) }

infixr 3 :&#
infixr 2 :|#

-- | Compositional Linear map representation. @L f g s@ denotes @f s -* g s@,
-- where @(-*)@ means linear functions.
data L :: (* -> *) -> (* -> *) -> (* -> *) where
  Zero :: L f g s
  Scale :: s -> L Par1 Par1 s
  (:|#) :: L f h s -> L g h s -> L (f :*: g) h s
  (:&#) :: L f h s -> L f k s -> L f (h :*: k) s
  JoinL :: V h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V h => h (L f g s) -> L f (h :.: g) s

instance Eq s => Eq (L f g s) where
  Zero == Zero            = True
  Zero == _               = False
  _ == Zero               = False
  (Scale s) == (Scale s') = s == s'
  (f :|# g) == (h :| k)   = (f == h) && (g == k)
  (f :&# g) == (h :& k)   = (f == h) && (g == k)
  ForkL ms  == Fork ms'   = and $ liftR2 (==) ms ms'
  JoinL ms  == Join ms'   = and $ liftR2 (==) ms ms'

-- Scalable vectors
class V a => HasScaleV a where
  scaleV :: Semiring s => s -> L a a s

type HasScaleV2 a b = (HasScaleV a, HasScaleV b)

instance HasScaleV Par1 where scaleV = Scale

instance (HasScaleV a, HasScaleV b) => HasScaleV (a :*: b) where
  scaleV s = scaleV s *** scaleV s

instance (HasScaleV a, HasScaleV b, Representable b) => HasScaleV (b :.: a) where
  scaleV s = cross (pureRep (scaleV s))

unjoin2 :: L (f :*: g) h s -> L f h s :* L g h s
unjoin2 Zero = (Zero,Zero)
unjoin2 (p :|# q) = (p,q)
unjoin2 ((unjoin2 -> (p,q)) :&# (unjoin2 -> (r,s))) = (p :& r, q :& s)
unjoin2 (ForkL ms) = (ForkL A.*** ForkL) (unzip (unjoin2 <$> ms))

-- unjoin2 ((p :| q) :&# (r :| s)) = (p :&# r, q :#& s)

-- Recursive pattern synonym definition with following bindings:
--   unjoin2 (defined at src/LinAlg.hs:(52,1)-(63,50))
--   :| (defined at src/LinAlg.hs:75:1-55)

#if 0
                               ForkL ms   :: L (f :*: g) (k :.: h) s
                                     ms   :: k (L (f :*: g) h s)
                          unjoin <$> ms   :: k (L f h s :* L g h s)
                   unzip (unjoin <$> ms)  :: k (L f h s) :* k (L g h s)
(ForkL *** ForkL) (unzip (unjoin <$> ms)) :: L f (k :.: h) s :* L g (k :.: h) s
#endif

unfork2 :: L f (h :*: k) s -> L f h s :* L f k s
unfork2 Zero = (Zero,Zero)
unfork2 (p :&# q) = (p,q)
unfork2 ((unfork2 -> (p,q)) :|# (unfork2 -> (r,s))) = (p :|# r, q :|# s)
unfork2 (JoinL ms) = (JoinL A.*** JoinL) (unzip (unfork2 <$> ms))

-- unfork2 ((p :& q) :|# (r :& s)) = (p :|# r, q :|# s)

pattern (:&) :: L f h s -> L f k s -> L f (h :*: k) s
pattern u :& v <- (unfork2 -> (u,v)) where (:&) = (:&#)
{-# complete (:&) #-}

pattern (:|) :: L f h s -> L g h s -> L (f :*: g) h s
pattern u :| v <- (unjoin2 -> (u,v)) where (:|) = (:|#)
{-# complete (:|) #-}

-- pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
-- pattern Join ms <- (unjoinL -> ms) where Join = JoinL
-- {-# complete Join #-}

unforkL :: Representable h => L f (h :.: g) s -> h (L f g s)
unforkL Zero       = pureRep Zero
unforkL (p :|# q)  = liftR2 (:|#) (unforkL p) (unforkL q)
unforkL (ForkL ms) = ms
unforkL (JoinL ms) = JoinL <$> distribute (unforkL <$> ms)

#if 0
-- Types for binary join clause
p :|# p' :: L (f :*: f') (h :.: g) s

                      p               :: L f  (h :.: g) s
                                  p'  :: L f' (h :.: g) s
              unforkL p               :: h (L f  g  s)
                          unforkL p'  :: h (L f' g  s)
liftR2 (:|#) (unforkL p) (unforkL p') :: h (L (f :*: f') g s)

-- Types for n-ary join clause:

     JoinL                     ms  :: L (k :.: f) (h :.: g) s
                               ms  :: k (L f (h :.: g) s)
                   unforkL <$> ms  :: k (h (L f g s))
          distrib (unforkL <$> ms) :: h (k (L f g s))
JoinL <$> distrib (unforkL <$> ms) :: h (L (k :.: f) g s)
#endif

unjoinL :: Representable h => L (h :.: f) g s -> h (L f g s)
unjoinL Zero       = pureRep Zero
unjoinL (p :&# p') = liftR2 (:&#) (unjoinL p) (unjoinL p')
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms) where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms) where Join = JoinL
{-# complete Join #-}

instance Additive s => Additive (L f g s) where
  zero = Zero
  Zero + m = m
  m + Zero = m
  Scale s + Scale s' = Scale (s + s') -- distributivity
  (f :|# g) + (h :| k) = (f + h) :| (g + k)
  (f :&# g) + (h :& k) = (f + h) :& (g + k)
  ForkL ms  + Fork ms' = Fork (ms +^ ms')
  JoinL ms  + Join ms' = Join (ms +^ ms')

-- | Row-major "matrix" of linear maps
rowMajor' :: (V2 f g, V2 h k) => k (h (L f g s)) -> L (h :.: f) (k :.: g) s
rowMajor' = Fork . fmap Join

-- | Row-major "matrix" of scalars
rowMajor :: (V f, V g) => g (f s) -> L (f :.: Par1) (g :.: Par1) s
rowMajor = rowMajor' . (fmap.fmap) Scale

diagR :: (Representable h, Eq (Rep h), Additive a) => h a -> h (h a)
diagR as =
  tabulate (\ i -> tabulate (\ j -> if i == j then as `index` i else zero))

idL :: (HasScaleV a, Semiring s) => L a a s
idL = scaleV one

class V a => Bang a where
  bang :: Semiring s => L a Par1 s

instance Bang Par1 where bang = Scale one

instance (Bang a, Bang b) => Bang (a :*: b) where
  bang = bang :|# bang

instance (Bang a, Bang b) => Bang (a :.: b) where
  bang = JoinL (pureRep bang)

-- Matrix transpose
tr :: L c r s -> L r c s
tr Zero = Zero
tr (Scale s) = Scale s
tr (a :|# b) = tr a :&# tr b
tr (a :&# b) = tr a :|# tr b
tr (ForkL m) = JoinL (fmap tr m)
tr (JoinL m) = ForkL (fmap tr m)

infixr 9 .@
(.@) :: Semiring s => L g h s -> L f g s -> L f h s
Zero      .@ _         = Zero                      -- Zero denotation
_         .@ Zero      = Zero                      -- linearity
Scale a   .@ Scale b   = Scale (a * b)             -- Scale denotation
(p :&# q) .@ m         = (p .@ m) :&# (q .@ m)     -- binary product law
m         .@ (p :|# q) = (m .@ p) :|# (m .@ q)     -- binary coproduct law
(r :|# s) .@ (p :&# q) = (r .@ p) + (s .@ q)       -- biproduct law
ForkL ms' .@ m         = ForkL (fmap (.@ m) ms')   -- n-ary product law
m'        .@ JoinL ms  = JoinL (fmap (m' .@) ms)   -- n-ary coproduct law
JoinL ms' .@ ForkL ms  = sum (ms' .^ ms)           -- biproduct law

(.^) :: (Representable p, Semiring s) => p (L g h s) -> p (L f g s) -> p (L f h s)
(.^) = liftR2 (.@)

instance (HasScaleV f, Semiring s) => Semiring (L f f s) where
  one = idL
  (*) = (.@)

-- Injections

inl :: (HasScaleV a, Semiring s) => L a (a :*: b) s
inl = idL :& zero

inr :: (HasScaleV b, Semiring s) => L b (a :*: b) s
inr = zero :& idL

-- Projections

exl :: (HasScaleV a, Semiring s) => L (a :*: b) a s
exl = idL :| zero

exr :: (HasScaleV b, Semiring s) => L (a :*: b) b s
exr = zero :| idL

-- Injections
ins :: (HasScaleV2 a c, Semiring s) => c (L a (c :.: a) s)
ins = unjoinL idL

-- Projections
exs :: (HasScaleV2 a c, Semiring s) => c (L (c :.: a) a s)
exs = unforkL idL

-- Binary biproduct bifunctor
(***) :: L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f *** g = (f :|# Zero) :&# (Zero :|# g)

(+++) :: L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f +++ g = (f :|# Zero) :&# (Zero :|# g)

-- N-ary biproduct bifunctor
cross :: (V a, HasScaleV2 b c, Semiring s) => c (L a b s) -> L (c :.: a) (c :.: b) s
cross fs = JoinL (ins .^ fs)

#if 0
-- Equivalently,

f *** g = (f :&# Zero) :|# (Zero :&# g)

(***) :: (HasScaleV2 a b, Semiring s) => L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f *** g = (f .@ exl) :&# (g .@ exr)

(***) :: (HasScaleV2 c d, Semiring s) => L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f *** g = (inl .@ f) :|# (inr .@ g)

-- Equivalently,
cross :: (V a, HasScaleV2 a c, Semiring s) => c (L a b s) -> L (c :.: a) (c :.: b) s
cross fs = ForkL (fs .^ exs)
#endif

-- Khatri-Rao projections

fstM :: (Semiring s, HasScaleV m, V k, Bang k) => L (m :.: k) (m :.: Par1) s
fstM = cross (pureRep bang)

sndM :: (Semiring s, HasScaleV k, V m) => L (m :.: k) k s
sndM = JoinL (pureRep idL)

-- Khatri Rao product (Matrix pairing)

khatri :: (Semiring s, Semiring (L f (m :.: k) s), Bang k, HasScaleV2 m k)
       => L f (m :.: Par1) s -> L f k s -> L f (m :.: k) s
khatri a b = (tr fstM .@ a) * (tr sndM .@ b)

