{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Generics.SOP.HKD.FromSOP where

import Data.Kind
import Generics.SOP.BasicFunctors
import Generics.SOP.Constraint
import Generics.SOP.HKD.Universe
import Generics.SOP.NP
import Generics.SOP.Universe

newtype FromSOP (g :: k -> Type) (h :: (k -> Type) -> Type) (f :: k -> Type) = FromSOP { unFromSOP :: h f }

instance
  ( g ~ f
  , xs ~ HKDCode (FromSOP g h)
  , IsProductType (h g) (ProductCode (h g))
  , AllZip (LiftedCoercible I f) (ProductCode (h g)) xs
  , AllZip (LiftedCoercible f I) xs (ProductCode (h g))
  ) => IsHKDFor (f :: k -> Type) (FromSOP (g :: k -> Type) (h :: (k -> Type) -> Type)) where
  type HKDCode (FromSOP g h) = StripF g (ProductCode (h g))

  hkdFrom :: FromSOP g h f -> NP f xs
  hkdFrom = fromI_NP . productTypeFrom . unFromSOP

  hkdTo :: NP f xs -> FromSOP g h f
  hkdTo = FromSOP . productTypeTo . toI_NP

type family StripF (f :: k -> Type) (xs :: [Type]) :: [k] where
  StripF f '[] = '[]
  StripF f (f x : xs) = x : StripF f xs

type family PlaceF (f :: k -> Type) (xs :: [k]) :: [k] where
  PlaceF f '[] = '[]
  PlaceF f (x : xs) = f x : PlaceF f xs

