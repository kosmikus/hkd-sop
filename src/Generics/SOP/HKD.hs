{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Generics.SOP.HKD where

import Data.Kind
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Universe
import qualified GHC.Generics as GHC
import Unsafe.Coerce

type HKD_ h f ys =
  ( IsProductType (h f) (ProductCode (h f))
  , AllZip (MkI f) ys (ProductCode (h f))
  , AllZip (UnI f) (ProductCode (h f)) ys
  , ys ~ StripF f (ProductCode (h f))
  , ProductCode (h f) ~ PlaceF f ys
  )

type StrangeHKD_ h f ys =
  ( IsProductType (h f) (ProductCode (h f))
  , AllZip (MkStrangeI f) ys (ProductCode (h f))
  , AllZip (UnStrangeI f) (ProductCode (h f)) ys
  , ys ~ StripStrangeF f (ProductCode (h f))
  , ProductCode (h f) ~ PlaceStrangeF f ys
  )

class HKD_ h f ys => IsHKD h f ys
instance HKD_ h f ys => IsHKD h f ys

hkdFrom_ :: IsHKD h f ys => h f -> NP f ys
hkdFrom_ x = uncoerce_NP_ (productTypeFrom x)

hkdTo_ :: IsHKD h f ys => NP f ys -> h f
hkdTo_ x = productTypeTo (mkcoerce_NP_ x)

pure_HKD_ :: forall h f ys . IsHKD h f ys => (forall a . f a) -> h f
pure_HKD_ f =
  hkdTo_ (pure_NP f :: NP f ys)

cpure_HKD_ :: forall c h f ys . (IsHKD h f ys, All c ys) => Proxy c -> (forall a . c a => f a) -> h f
cpure_HKD_ p f =
  hkdTo_ (cpure_NP p f :: NP f ys)

map_HKD_ :: forall h f g ys . (IsHKD h f ys, IsHKD h g ys) => (forall a . f a -> g a) -> h f -> h g
map_HKD_ f =
  hkdTo_ . (map_NP f :: NP f ys -> NP g ys) . hkdFrom_

cmap_HKD_ :: forall c h f g ys . (IsHKD h f ys, IsHKD h g ys, All c ys) => Proxy c -> (forall a . c a => f a -> g a) -> h f -> h g
cmap_HKD_ p f =
  hkdTo_ . (cmap_NP p f :: NP f ys -> NP g ys) . hkdFrom_

ctraverse_HKD_ :: forall c h f g ys . (IsHKD h f ys, IsHKD h I ys, All c ys, Applicative g) => Proxy c -> (forall a . c a => f a -> g a) -> h f -> g (h I)
ctraverse_HKD_ p f =
  (hkdTo_ <$>) . (ctraverse_NP p f :: NP f ys -> g (NP I ys)) . hkdFrom_

data Foo f =
  MkFoo
    (f Int)
    (f Bool)
  deriving stock (GHC.Generic)
  deriving anyclass Generic
  -- deriving (HKD f) via FromSOP f Foo

deriving via FromSOP f Foo instance HKD f Foo

data Bar f =
  MkBar
    (f Char)
    (Foo f)
  deriving stock (GHC.Generic)
  deriving anyclass Generic

instance HKD f Bar where
  type HKDCode Bar = '[ Char, Int, Bool ]

  hkdFrom (MkBar c foo) = c :* hkdFrom foo
  hkdTo (c :* xs) = MkBar c (hkdTo xs)

data Baz f =
  MkBaz
    (Strange f Int)
    (Strange f Bool)
  deriving stock (GHC.Generic)
  deriving anyclass Generic

type family Strange (f :: k -> Type) (x :: k) :: Type where
  Strange I x = x
  Strange f x = f x

-- deriving via FromStrangeSOP f Baz instance IsStrange f => HKD f Baz
-- deriving via FromSOP f Baz instance (SListI (StripF f '[Strange f Int, Strange f Bool])) => HKD f Baz

{-
instance IsStrange f => HKD f Baz where
  type HKDCode Baz = '[ Int, Bool ]

  hkdFrom (MkBaz i b) = unstrange i :* unstrange b :* Nil
  hkdTo (i :* b :* Nil) = MkBaz (strange i) (strange b)
-}

class IsStrange (f :: k -> Type) where
  unstrange :: Strange f x -> f x
  strange   :: f x -> Strange f x

instance (b ~ IsEqual f I, forall x . IsStrangeAux b f x) => IsStrange f where
  unstrange = unstrangeAux (Proxy @(IsEqual f I))
  strange = strangeAux (Proxy @(IsEqual f I))

class IsStrangeAux (b :: Bool) (f :: k -> Type) (x :: k) where
  unstrangeAux :: Proxy b -> Strange f x -> f x
  strangeAux   :: Proxy b -> f x -> Strange f x

type family IsEqual (a :: k1) (b :: k2) :: Bool where
  IsEqual a a = True
  IsEqual _ _ = False

instance (f ~ I) => IsStrangeAux True f x where
  unstrangeAux _ x = I x
  strangeAux   _ (I x) = x

instance (Strange f x ~ f x) => IsStrangeAux False f x where
  unstrangeAux _ x = x
  strangeAux   _ x = x

sample :: Foo Maybe
sample = MkFoo Nothing Nothing

deriving instance (Show (f Int), Show (f Bool)) => Show (Foo f)

class {- (SListI (HKDCode h)) => -} HKD (f :: k -> Type) (h :: (k -> Type) -> Type) where

  type HKDCode h :: [k]

  hkdFrom :: h f -> NP f (HKDCode h)
  hkdTo :: NP f (HKDCode h) -> h f

newtype FromSOP (g :: k -> Type) (h :: (k -> Type) -> Type) (f :: k -> Type) = FromSOP (h f)
newtype FromStrangeSOP (g :: k -> Type) (h :: (k -> Type) -> Type) (f :: k -> Type) = FromStrangeSOP (h f)

instance
  ( HKD_ h f ys
  , SListI ys
  , StripF g (ProductCode (h g)) ~ ys
  , f ~ g
  ) => HKD f (FromSOP g h) where

  type HKDCode (FromSOP g h) = StripF g (ProductCode (h g))

  hkdFrom (FromSOP x) = hkdFrom_ x
  hkdTo x = FromSOP (hkdTo_ x)

instance
  ( StrangeHKD_ h f ys
  , SListI ys
  , StripStrangeF g (ProductCode (h g)) ~ ys
  , f ~ g
  , IsStrange f
  ) => HKD f (FromStrangeSOP g h) where

  type HKDCode (FromStrangeSOP g h) = StripStrangeF g (ProductCode (h g))

  hkdFrom (FromStrangeSOP x) = trans_NP (Proxy @(UnStrangeI f)) (unstrange . unI) (productTypeFrom x)
  hkdTo x = FromStrangeSOP (productTypeTo (trans_NP (Proxy @(MkStrangeI f)) (I . strange) x))

class (forall f . HKD f h, SListI (HKDCode h)) => TrueHKD (h :: (k -> Type) -> Type)
instance (forall f . HKD f h, SListI (HKDCode h)) => TrueHKD (h :: (k -> Type) -> Type)

{-
instance
  ( IsProductType (h f) (ProductCode (h f))
  , SameShapeAs (ProductCode (h f)) ys
  , SameShapeAs ys (ProductCode (h f))
  , AllZip (LiftedCoercible I f) (ProductCode (h f)) ys
  ) => HKD (FromSOP h) f ys where

  type HKDCode (FromSOP h) = ys

  hkdFrom :: forall f . FromSOP h f -> NP f (HKDCode (FromSOP h))
  hkdFrom (FromSOP x) = coerce_NP (undefined x :: NP I (ProductCode (h f)))
-}

pure_HKD :: forall h f . TrueHKD h => (forall a . f a) -> h f
pure_HKD f =
  hkdTo (pure_NP f)

map_HKD :: forall h f g . TrueHKD h => (forall (a :: k) . f a -> g a) -> h f -> h g
map_HKD f =
  hkdTo . map_NP f . hkdFrom

sequence_HKD :: forall h f . (TrueHKD h, Applicative f) => h f -> f (h I)
sequence_HKD =
  (hkdTo <$>) . sequence_NP . hkdFrom

class (fx ~ f x) => UnI (f :: k -> Type) (fx :: Type) (x :: k)
instance (fx ~ f x) => UnI (f :: k -> Type) (fx :: Type) (x :: k)

class (f x ~ fx) => MkI (f :: k -> Type) (x :: k) (fx :: Type)
instance (f x ~ fx) => MkI (f :: k -> Type) (x :: k) (fx :: Type)

class (fx ~ Strange f x) => UnStrangeI (f :: k -> Type) (fx :: Type) (x :: k)
instance (fx ~ Strange f x) => UnStrangeI (f :: k -> Type) (fx :: Type) (x :: k)

class (Strange f x ~ fx) => MkStrangeI (f :: k -> Type) (x :: k) (fx :: Type)
instance (Strange f x ~ fx) => MkStrangeI (f :: k -> Type) (x :: k) (fx :: Type)

type family StripF (f :: k -> Type) (xs :: [k]) :: [k] where
  StripF f '[] = '[]
  StripF f (f x : xs) = x : StripF f xs

type family PlaceF (f :: k -> Type) (xs :: [k]) :: [k] where
  PlaceF f '[] = '[]
  PlaceF f (x : xs) = f x : PlaceF f xs

type family StripStrangeF (f :: k -> Type) (xs :: [k]) :: [k] where
  StripStrangeF f '[] = '[]
  StripStrangeF I (x : xs) = x : StripStrangeF I xs
  StripStrangeF f (f x : xs) = x : StripStrangeF f xs

type family PlaceStrangeF (f :: k -> Type) (xs :: [k]) :: [k] where
  PlaceStrangeF f '[] = '[]
  PlaceStrangeF I (x : xs) = x : PlaceStrangeF I xs
  PlaceStrangeF f (x : xs) = f x : PlaceStrangeF f xs

mkcoerce_NP_ :: forall (f :: k -> Type) (xs :: [k]) (ys :: [Type]) . AllZip (MkI f) xs ys => NP f xs -> NP I ys
mkcoerce_NP_ = trans_NP (Proxy @(MkI f)) (\ x -> I x)

uncoerce_NP_ :: forall (f :: k -> Type) (xs :: [Type]) (ys :: [k]) . AllZip (UnI f) xs ys => NP I xs -> NP f ys
uncoerce_NP_ = trans_NP (Proxy @(UnI f)) (\ (I x) -> x)

