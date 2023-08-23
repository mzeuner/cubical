{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.LocRingedLattice.Instances.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty renaming (IsZarMap to isSupport ; isPropIsZarMap to isPropIsSupport)
open import Cubical.Algebra.ZariskiLattice.StructureSheaf

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.LocRingedLattice.Base

open Iso
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level


module _ (R : CommRing ℓ) where
  open ZarLat
  open LocRingedLattice

  DLSpec : LocRingedLattice ℓ
  L DLSpec = ZariskiLattice R
  𝓕 DLSpec = 𝓞 R
  isSheaf𝓕 DLSpec = isSheaf𝓞 R
  𝓓 DLSpec = {!!}
  isSupport𝓓 DLSpec = {!!}
  isInvMap𝓓 DLSpec = {!!}
