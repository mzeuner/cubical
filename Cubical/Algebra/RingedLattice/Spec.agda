{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.RingedLattice.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty
open import Cubical.Algebra.ZariskiLattice.StructureSheaf

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice

open import Cubical.Categories.DistLatticeSheaf.Base

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Algebra.RingedLattice.Base
open import Cubical.Algebra.RingedLattice.Properties

private
  variable
    ℓ : Level

module _ where
  open Functor
  open RingedLattice
  open RingedLatticeHom
  open ZarLat
  open ZarLatUniversalProp

  Spec : CommRing ℓ → RingedLattice ℓ
  L (Spec R) = ZariskiLattice R
  𝓕 (Spec R) = 𝓞 R
  isSheaf𝓕 (Spec R) = isSheaf𝓞 R

  -- can we use the comparison lemma for dist. lattices?
  homSpec : {A B : CommRing ℓ} → CommRingHom A B → RingedLatticeHom (Spec A) (Spec B)
  π (homSpec φ) = inducedZarLatHom φ
  π♯ (homSpec φ) = {!!}
  isNatπ♯ (homSpec φ) = {!!}
