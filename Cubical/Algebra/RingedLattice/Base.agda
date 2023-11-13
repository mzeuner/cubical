{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.RingedLattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice

open import Cubical.Categories.DistLatticeSheaf.Base

open import Cubical.Reflection.RecordEquiv

open Functor

private
  variable
    ℓ ℓ' : Level

record RingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ
    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕

-- make this universe polymorphic by splitting up "natural transformation" π♯
record RingedLatticeHom (Y : RingedLattice ℓ) (X : RingedLattice ℓ') : Type (ℓ-max ℓ ℓ') where
  open RingedLattice
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (Y .L)))
  field
    π : DistLatticeHom (Y .L) (X .L)
    π♯ : (u : Y .L .fst) → CommRingHom (Y .𝓕 .F-ob u) (X .𝓕 .F-ob (π .fst u))
    isNatπ♯ : ∀ (u v : Y .L .fst) (u≥v : v ≤ u)
            → π♯ v ∘cr (Y .𝓕 .F-hom u≥v) ≡ (X .𝓕 .F-hom (pres≤ π u≥v)) ∘cr π♯ u


unquoteDecl RingedLatticeHomIsoΣ = declareRecordIsoΣ RingedLatticeHomIsoΣ (quote RingedLatticeHom)

isSetRingedLatticeHom : (Y : RingedLattice ℓ) (X : RingedLattice ℓ') → isSet (RingedLatticeHom Y X)
isSetRingedLatticeHom _ _ = isOfHLevelRetractFromIso 2 RingedLatticeHomIsoΣ
                              (isSetΣ (isSetLatticeHom _ _)
                                λ _ → isSetΣSndProp (isSetΠ (λ _ → isSetRingHom _ _))
                                  λ _ → isPropΠ3 (λ _ _ _ → isSetRingHom _ _ _ _))


open RingedLattice
open RingedLatticeHom

RingedLatticeHom≡ : {Y : RingedLattice ℓ} {X : RingedLattice ℓ'} (f g : RingedLatticeHom Y X)
  → (p : f .π ≡ g .π)
  → (q : ∀ (u : Y .L .fst)
       → PathP (λ i → CommRingHom (Y .𝓕 .F-ob u) (X .𝓕 .F-ob (p i .fst u)))
               (f .π♯ u) (g .π♯ u))
  → f ≡ g
π (RingedLatticeHom≡ f g p q i) = p i
π♯ (RingedLatticeHom≡ f g p q i) u = q u i
isNatπ♯ (RingedLatticeHom≡ {Y = Y} {X = X} f g p q i) u v u≥v =
  isProp→PathP
    {B = λ i → q v i ∘cr Y .𝓕 .F-hom u≥v ≡ X .𝓕 .F-hom (pres≤ (p i) u≥v) ∘cr q u i}
    (λ _ → isSetRingHom _ _ _ _) (f .isNatπ♯ u v u≥v) (g .isNatπ♯ u v u≥v) i
