{-# OPTIONS --safe #-}
module Cubical.Algebra.DistLattice.DownSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice.Base

open Iso

private
  variable
    ℓ ℓ' : Level

module _ (L' : DistLattice ℓ) where

  open DistLatticeStr ⦃...⦄
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
  --open Join L'
  open Order (DistLattice→Lattice L')
  --open PosetStr using (is-prop-valued)

  private
    L = L' .fst
    instance _ = L' .snd


  -- ↓ᴾ : L → ℙ L
  -- ↓ᴾ u v = (v ≤ u) , is-set _ _
  -- should be done for posets first I guess...
  ↓ : L → Type ℓ
  ↓ u = Σ[ v ∈ L ] v ≤ u
