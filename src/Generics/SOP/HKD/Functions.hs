module Generics.SOP.HKD.Functions where

import Data.Kind
import Generics.SOP.BasicFunctors
import Generics.SOP.Classes
import Generics.SOP.Constraint
import Generics.SOP.HKD.Universe
import Generics.SOP.NP

pure_HKD ::
  forall f h . HKD h
  => (forall a . f a)
  -> h f
pure_HKD f =
  hkdTo (pure_NP f)

cpure_HKD ::
  forall c f h proxy . (HKD h, All c (HKDCode h))
  => proxy c
  -> (forall a . c a => f a)
  -> h f
cpure_HKD p f =
  hkdTo (cpure_NP p f)

collapse_HKD ::
  forall h a . HKD h
  => h (K a)
  -> [a]
collapse_HKD =
  collapse_NP . hkdFrom

type Projection_HKD (f :: k -> Type) (h :: (k -> Type) -> Type) =
  K (h f) -.-> f

projections_HKD ::
  forall f h . HKD h
  => h (Projection_HKD f h)
projections_HKD =
  hkdTo
    (map_NP
      (\ (Fn f) -> Fn (f . mapKK hkdFrom))
      (projections :: NP (Projection f (HKDCode h)) (HKDCode h))
    )

map_HKD ::
  forall f g h . HKD h
  => (forall a . f a -> g a)
  -> h f -> h g
map_HKD f =
  hkdTo . map_NP f . hkdFrom

cmap_HKD ::
  forall c f g h proxy . (HKD h, All c (HKDCode h))
  => proxy c
  -> (forall a . c a => f a -> g a)
  -> h f
  -> h g
cmap_HKD p f =
  hkdTo . cmap_NP p f . hkdFrom

zipWith_HKD ::
  forall e f g h . HKD h
  => (forall a . e a -> f a -> g a)
  -> h e -> h f -> h g
zipWith_HKD f x y =
  hkdTo (zipWith_NP f (hkdFrom x) (hkdFrom y))

czipWith_HKD ::
  forall c e f g h proxy . (HKD h, All c (HKDCode h))
  => proxy c
  -> (forall a . c a => e a -> f a -> g a)
  -> h e -> h f -> h g
czipWith_HKD p f x y =
  hkdTo (czipWith_NP p f (hkdFrom x) (hkdFrom y))

traverse__HKD ::
  forall f g h . (HKD h, Applicative g)
  => (forall a . f a -> g ())
  -> h f -> g ()
traverse__HKD f =
  traverse__NP f . hkdFrom

ctraverse__HKD ::
  forall c f g h proxy . (HKD h, All c (HKDCode h), Applicative g)
  => proxy c
  -> (forall a . c a => f a -> g ())
  -> h f -> g ()
ctraverse__HKD p f =
  ctraverse__NP p f . hkdFrom

traverse'_HKD ::
  forall f f' g h . (HKD h, Applicative g)
  => (forall a . f a -> g (f' a))
  -> h f -> g (h f')
traverse'_HKD f =
  (hkdTo <$>) . traverse'_NP f . hkdFrom

ctraverse'_HKD ::
  forall c f f' g h proxy . (HKD h, All c (HKDCode h), Applicative g)
  => proxy c
  -> (forall a . c a => f a -> g (f' a))
  -> h f -> g (h f')
ctraverse'_HKD p f =
  (hkdTo <$>) . ctraverse'_NP p f . hkdFrom

sequence_HKD ::
  forall f h . (HKD h, Applicative f)
  => h f
  -> f (h I)
sequence_HKD =
  (hkdTo <$>) . sequence_NP . hkdFrom

sequence'_HKD ::
  forall f g h . (HKD h, Applicative f)
  => h (f :.: g)
  -> f (h g)
sequence'_HKD =
  (hkdTo <$>) . sequence'_NP . hkdFrom

trans_HKD ::
  forall c f1 f2 h1 h2 proxy . (HKD h1, HKD h2, AllZip c (HKDCode h1) (HKDCode h2))
  => proxy c
  -> (forall x1 x2 . c x1 x2 => f1 x1 -> f2 x2)
  -> h1 f1
  -> h2 f2
trans_HKD p f =
  hkdTo . trans_NP p f . hkdFrom

ap_HKD ::
  forall f g h . (HKD h)
  => h (f -.-> g) -> h f -> h g
ap_HKD f x =
  hkdTo (ap_NP (hkdFrom f) (hkdFrom x))
