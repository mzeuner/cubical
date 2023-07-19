{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.SIP

-- open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

-- open import Cubical.Displayed.Base
-- open import Cubical.Displayed.Auto
-- open import Cubical.Displayed.Record
-- open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis

open import Cubical.Algebra.ZariskiLattice.UniversalProperty renaming (IsZarMap to isSupport ; isPropIsZarMap to isPropIsSupport)

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

-- open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.LocRingedLattice.Base

open Iso
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level


module _
         {ℓ : Level}
         (L' : DistLattice ℓ)
         (B' : ℙ (fst L'))
         (isBasisB : IsBasis L' B')

         (𝓕 : Functor ((DistLatticeCategory L') ^op) (CommRingsCategory {ℓ}))
         (isSheaf𝓕 : isDLSheaf L' _ 𝓕)
         where

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
  private
    L = fst L'
    B = Σ[ u ∈ L ] (u ∈ B')
    -- LPos = JoinSemilattice.IndPoset (Lattice→JoinSemilattice (DistLattice→Lattice L'))
    -- BPos = MeetSemilattice.IndPoset (Basis→MeetSemilattice L' B' isBasisB)

  InvMapFromBasis :
      (𝓓ᴮ : (u : B) → 𝓕 .F-ob (u .fst) .fst → B)
      (𝓓ᴮ≤ : (u : B) (s : 𝓕 .F-ob (u .fst) .fst) → 𝓓ᴮ u s .fst ≤ (u .fst))
      (≤𝓓ᴮToInv : (u v : B) (s : 𝓕 .F-ob (u .fst) .fst) (v≤u : v .fst ≤ (u .fst))
                → v .fst ≤ 𝓓ᴮ u s .fst → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob (v .fst)) ˣ)
      (≤𝓓ᴮFromInv : (u v : B) (s : 𝓕 .F-ob (u .fst) .fst) (v≤u : v .fst ≤ (u .fst))
                  → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob (v .fst)) ˣ → v .fst ≤ 𝓓ᴮ u s .fst)
    → InvMap L' 𝓕
  InvMapFromBasis = {!!}
