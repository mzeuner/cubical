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
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.HITs.PropositionalTruncation as PT
-- open import Cubical.Displayed.Base
-- open import Cubical.Displayed.Auto
-- open import Cubical.Displayed.Record
-- open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps
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
  open Join L'
  private
    L = fst L'
    B = Σ[ u ∈ L ] (u ∈ B')
    -- LPos = JoinSemilattice.IndPoset (Lattice→JoinSemilattice (DistLattice→Lattice L'))
    -- BPos = MeetSemilattice.IndPoset (Basis→MeetSemilattice L' B' isBasisB)

  module _
    (𝓓ᴮ : (u : B) → 𝓕 .F-ob (u .fst) .fst → B)
    (𝓓ᴮ≤ : (u : B) (s : 𝓕 .F-ob (u .fst) .fst) → 𝓓ᴮ u s .fst ≤ (u .fst))
    (≤𝓓ᴮToInv : (u : B) (s : 𝓕 .F-ob (u .fst) .fst) (v : B) (v≤u : v .fst ≤ (u .fst))
              → v .fst ≤ 𝓓ᴮ u s .fst → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob (v .fst)) ˣ)
    (≤𝓓ᴮFromInv : (u : B) (s : 𝓕 .F-ob (u .fst) .fst) (v : B) (v≤u : v .fst ≤ (u .fst))
                → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob (v .fst)) ˣ → v .fst ≤ 𝓓ᴮ u s .fst)
    where
    open IsBasis isBasisB
    InvMapFromBasisStage : (u : L) → InvMapAtStage L' 𝓕 u
    InvMapFromBasisStage u = PT.rec (isPropInvMapAtStage L' 𝓕 u) helperΣ (⋁Basis u)
      where
      helperΣ : Σ[ n ∈ ℕ ] Σ[ α ∈ FinVec L n ] (∀ i → α i ∈ B') × (⋁ α ≡ u)
              → InvMapAtStage L' 𝓕 u
      helperΣ (n , α , α∈B , ⋁α≡u) = 𝓓ᵤ , {!!}
        where
        α≤u : ∀ i → α i ≤ u
        α≤u i = subst (λ x → α i ≤ x) ⋁α≡u (ind≤bigOp α i)

        𝓓ᵤ : 𝓕 .F-ob u .fst → L
        𝓓ᵤ s = ⋁ (λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst)
             -- 𝓓ᵤ s = ⋁ᵢ 𝓓ᴮ(s ↿ αᵢ)
