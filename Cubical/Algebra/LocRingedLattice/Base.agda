{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

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

open import Cubical.Reflection.RecordEquiv

open Iso
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level

-- locality on the stalks in terms of supports
module _ {ℓ : Level} (L : DistLattice ℓ)
         (𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})) where

  open Order (DistLattice→Lattice L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open PosetStr (IndPoset .snd) hiding (_≤_)

  -- "invertibility support"
  record IsInvSupport (𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst) : Type ℓ where
    field
      isSupport𝓓 : ∀ u → isSupport (𝓕 .F-ob u) L (𝓓 u)
      𝓓≤ : (u : L .fst) (s : 𝓕 .F-ob u .fst) → 𝓓 u s ≤ u
      ≤𝓓ToInv : (u v : L .fst) (s : 𝓕 .F-ob u .fst) (v≤u : v ≤ u)
              → v ≤ 𝓓 u s → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob v) ˣ
      ≤𝓓FromInv : (u v : L .fst) (s : 𝓕 .F-ob u .fst) (v≤u : v ≤ u)
                → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob v) ˣ → v ≤ 𝓓 u s

  unquoteDecl IsInvSupportIsoΣ = declareRecordIsoΣ IsInvSupportIsoΣ (quote IsInvSupport)
  open IsInvSupport

  isPropIsInvSupport : ∀ 𝓓 → isProp (IsInvSupport 𝓓)
  isPropIsInvSupport 𝓓 = isOfHLevelRetractFromIso 1 IsInvSupportIsoΣ
                           (isProp×3 (isPropΠ λ _ → isPropIsSupport _ _ _)
                                     (isPropΠ2 (λ _ _ → is-prop-valued _ _))
                                     (isPropΠ5 (λ _ _ _ _ _ → ∈-isProp ((𝓕 .F-ob _) ˣ) _))
                                     (isPropΠ5 λ _ _ _ _ _ → is-prop-valued _ _))

record LocRingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ

    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕

    𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst
    isInvSupport𝓓 : IsInvSupport L 𝓕 𝓓


record LocRingedLatticeHom (Y X : LocRingedLattice ℓ) : Type ℓ where
  open LocRingedLattice
  field
    π : DistLatticeHom (Y .L) (X .L)
    π♯ : NatTrans (Y .𝓕) ((X .𝓕) ∘F ((DistLatticeFunc (Y .L) (X .L) π) ^opF))
    pres𝓓 : {u : Y .L .fst} (s : Y .𝓕 .F-ob u .fst)
          → π .fst (Y .𝓓 u s) ≡ X .𝓓 (π .fst u) (π♯ .N-ob u .fst s)
