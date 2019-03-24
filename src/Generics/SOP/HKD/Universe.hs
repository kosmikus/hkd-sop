{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Generics.SOP.HKD.Universe where

import Data.Kind
import Generics.SOP


type family HKDCode (h :: (k -> Type) -> Type) :: [k]

class IsHKDFor (f :: k -> Type) (h :: (k -> Type) -> Type) where
  hkdFrom :: h f -> NP f (HKDCode h)
  hkdTo :: NP f (HKDCode h) -> h f

class (forall f . IsHKDFor f h, SListI (HKDCode h)) => HKD (h :: (k -> Type) -> Type)
instance (forall f . IsHKDFor f h, SListI (HKDCode h)) => HKD h
