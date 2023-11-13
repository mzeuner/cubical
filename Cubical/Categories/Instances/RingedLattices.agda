{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.RingedLattices where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingedLattice

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open Category hiding (_∘_)
open Functor
open RingedLattice
open RingedLatticeHom

private
  variable
    ℓ ℓ' ℓ'' : Level

RingedLatticesCategory : Category (ℓ-suc ℓ) ℓ
ob RingedLatticesCategory                     = RingedLattice _
Hom[_,_] RingedLatticesCategory               = RingedLatticeHom
id RingedLatticesCategory {X}                 = idRingedLatticeHom X
_⋆_ RingedLatticesCategory {X} {Y} {Z}        = compRingedLatticeHom X Y Z
⋆IdL RingedLatticesCategory {X} {Y}           = compIdRingedLatticeHom {X = X} {Y}
⋆IdR RingedLatticesCategory {X} {Y}           = idCompRingedLatticeHom {X = X} {Y}
⋆Assoc RingedLatticesCategory {X} {Y} {Z} {W} = compAssocRingedLatticeHom {X = X} {Y} {Z} {W}
isSetHom RingedLatticesCategory               = isSetRingedLatticeHom _ _
