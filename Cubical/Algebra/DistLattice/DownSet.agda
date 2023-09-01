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

open import Cubical.Relation.Binary.Poset

open Iso

private
  variable
    ℓ ℓ' : Level

module _ (L' : DistLattice ℓ) where

  open DistLatticeStr ⦃...⦄
  open PosetStr ⦃...⦄ hiding (is-set)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L')) hiding (_≤_ ; IndPoset)
  open LatticeTheory (DistLattice→Lattice L')
  --open Join L'
  open Order (DistLattice→Lattice L')
  open PosetDownset IndPoset


  private
    L = L' .fst
    LPoset = IndPoset
    instance
      _ = L' .snd
      _ = LPoset .snd

  ↓ᴰᴸ : L → DistLattice ℓ
  fst (↓ᴰᴸ u) = ↓ u
  DistLatticeStr.0l (snd (↓ᴰᴸ u)) = 0l , ∨lLid u
  DistLatticeStr.1l (snd (↓ᴰᴸ u)) = u , is-refl u
  DistLatticeStr._∨l_ (snd (↓ᴰᴸ u)) (v , v≤u) (w , w≤u) =
    v ∨l w , ∨lIsMax _ _ _ v≤u w≤u
  DistLatticeStr._∧l_ (snd (↓ᴰᴸ u)) (v , v≤u) (w , _) =
    v ∧l w , is-trans _ _ _ (≤m→≤j _ _ (∧≤RCancel _ _)) v≤u
  DistLatticeStr.isDistLattice (snd (↓ᴰᴸ u)) = makeIsDistLattice∧lOver∨l
    (isSetΣSndProp is-set λ _ → is-prop-valued _ _)
    (λ _ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∨lAssoc _ _ _))
    (λ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∨lRid _))
    (λ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∨lComm _ _))
    (λ _ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∧lAssoc _ _ _))
    (λ (_ , v≤u) → Σ≡Prop (λ _ → is-prop-valued _ _) (≤j→≤m _ _ v≤u))
    (λ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∧lComm _ _))
    (λ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∧lAbsorb∨l _ _))
    (λ _ _ _ → Σ≡Prop (λ _ → is-prop-valued _ _) (∧lLdist∨l _ _ _))
