{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.RingedLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Functor

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Algebra.RingedLattice.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
  open Functor
  open RingedLattice
  open RingedLatticeHom


  idRingedLatticeHom : (X : RingedLattice ℓ) → RingedLatticeHom X X
  π (idRingedLatticeHom X) = idDistLatticeHom (X .L)
  π♯ (idRingedLatticeHom X) u = idCommRingHom (X .𝓕 .F-ob u)
  isNatπ♯ (idRingedLatticeHom X) u v u≥v =
    idCommRingHom (X .𝓕 .F-ob v) ∘cr X .𝓕 .F-hom u≥v ≡⟨ idCompCommRingHom _ ⟩
    X .𝓕 .F-hom u≥v ≡⟨ cong (X .𝓕 .F-hom) (is-prop-valued _ _ _ _) ⟩
    X .𝓕 .F-hom (pres≤ (idDistLatticeHom (X .L)) u≥v) ≡⟨ sym (compIdCommRingHom _) ⟩
    X .𝓕 .F-hom (pres≤ (idDistLatticeHom (X .L)) u≥v) ∘cr idCommRingHom (X .𝓕 .F-ob u) ∎
    where
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (X .L)))
    open PosetStr (IndPoset .snd)


  compRingedLatticeHom : (X Y Z : RingedLattice ℓ)
                         --(Y : RingedLattice ℓ') (Z : RingedLattice ℓ'')
                       → RingedLatticeHom X Y → RingedLatticeHom Y Z → RingedLatticeHom X Z
  π (compRingedLatticeHom X Y Z f g) = compDistLatticeHom _ _ _ (f .π) (g .π)
  π♯ (compRingedLatticeHom X Y Z f g) u = compCommRingHom _ _ _ (f .π♯ u)
                                                                (g .π♯ (f .π .fst u))
  isNatπ♯ (compRingedLatticeHom X Y Z f g) u v u≥v =
      (g .π♯ (f .π .fst v) ∘cr f .π♯ v) ∘cr X .𝓕 .F-hom u≥v
    ≡⟨ sym (compAssocCommRingHom _ _ _) ⟩
      g .π♯ (f .π .fst v) ∘cr (f .π♯ v ∘cr X .𝓕 .F-hom u≥v)
    ≡⟨ cong (g .π♯ (f .π .fst v) ∘cr_) (f .isNatπ♯ _ _ u≥v) ⟩
      g .π♯ (f .π .fst v) ∘cr (Y .𝓕 .F-hom (pres≤ (f .π) u≥v) ∘cr f .π♯ u)
    ≡⟨ compAssocCommRingHom _ _ _ ⟩
      (g .π♯ (f .π .fst v) ∘cr Y .𝓕 .F-hom (pres≤ (f .π) u≥v)) ∘cr f .π♯ u
    ≡⟨ cong (_∘cr (f .π♯ u)) (g .isNatπ♯ _ _ (pres≤ (f .π) u≥v)) ⟩
      (Z .𝓕 .F-hom (pres≤ (g .π) (pres≤ (f .π) u≥v)) ∘cr g .π♯ (f .π .fst u)) ∘cr f .π♯ u
    ≡⟨ sym (compAssocCommRingHom _ _ _) ⟩
      Z .𝓕 .F-hom (pres≤ (g .π) (pres≤ (f .π) u≥v)) ∘cr (g .π♯ (f .π .fst u) ∘cr f .π♯ u)
    ≡⟨ cong (λ x → Z .𝓕 .F-hom x ∘cr (g .π♯ (f .π .fst u) ∘cr f .π♯ u))
            (is-prop-valued _ _ _ _) ⟩
      Z .𝓕 .F-hom (pres≤ (g .π ∘dl f .π) u≥v) ∘cr (g .π♯ (f .π .fst u) ∘cr f .π♯ u) ∎
    where
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (Z .L)))
    open PosetStr (IndPoset .snd)


  _∘rl_ : {X Y Z : RingedLattice ℓ} --{Y : RingedLattice ℓ'} {Z : RingedLattice ℓ''}
        → RingedLatticeHom Y Z → RingedLatticeHom X Y → RingedLatticeHom X Z
  g ∘rl f = compRingedLatticeHom _ _ _ f g

  compIdRingedLatticeHom : {X Y : RingedLattice ℓ} (f : RingedLatticeHom X Y)
                         → compRingedLatticeHom _ _ _ (idRingedLatticeHom X) f ≡ f
  compIdRingedLatticeHom _ = RingedLatticeHom≡ _ _ (compIdDistLatticeHom _)
                                                   (λ _  → compIdCommRingHom _)

  idCompRingedLatticeHom : {X Y : RingedLattice ℓ} (f : RingedLatticeHom X Y)
                         → compRingedLatticeHom _ _ _ f (idRingedLatticeHom Y) ≡ f
  idCompRingedLatticeHom _ = RingedLatticeHom≡ _ _ (idCompDistLatticeHom _)
                                                   (λ _  → idCompCommRingHom _)

  compAssocRingedLatticeHom : {X Y Z U : RingedLattice ℓ}
                              (f : RingedLatticeHom X Y)
                              (g : RingedLatticeHom Y Z)
                              (h : RingedLatticeHom Z U)
                            → compRingedLatticeHom _ _ _ (compRingedLatticeHom _ _ _ f g) h
                            ≡ compRingedLatticeHom _ _ _ f (compRingedLatticeHom _ _ _ g h)
  compAssocRingedLatticeHom _ _ _ = RingedLatticeHom≡ _ _ (compAssocDistLatticeHom _ _ _)
                                                      (λ _  → compAssocCommRingHom _ _ _)
