{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
--open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData

open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.CommRings

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base


private
  variable
    ℓ ℓ' ℓ'' : Level

module RingedLatticeTheory (L : DistLattice ℓ)
                           (𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ}))
                           (isSheaf𝓕 : isDLSheaf L _ 𝓕)
                           where

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open Join L
  open Order (DistLattice→Lattice L)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  open Category
  open Functor

  private
    Lᵒᵖ = (DistLatticeCategory L) ^op


  module _ (u : Lᵒᵖ .ob) (s : 𝓕 .F-ob u .fst)
           {n : ℕ} (α : FinVec (L .fst) n) (⋁α≡u : ⋁ α ≡ u) where

    private
      α≤u : ∀ i → α i ≤ u
      α≤u i = subst (λ x → α i ≤ x) ⋁α≡u (ind≤bigOp α i)

      s↿ : (i : Fin n) → 𝓕 .F-ob (α i) .fst
      s↿ i = 𝓕 .F-hom (α≤u i) .fst s

    invToRestInv : s ∈ 𝓕 .F-ob u ˣ
                 → ∀ i → s↿ i ∈ 𝓕 .F-ob (α i) ˣ
    invToRestInv sInv i = RingHomRespInv _ ⦃ sInv ⦄
      where
      open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _} (𝓕 .F-hom (α≤u i))

    invFromRestInv : (∀ i → s↿ i ∈ 𝓕 .F-ob (α i) ˣ)
                   → s ∈ 𝓕 .F-ob u ˣ
    invFromRestInv s↿Inv = {!!}
