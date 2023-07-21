{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Functions.FunExtEquiv

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
open import Cubical.Categories.Instances.Poset

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



module _ {ℓ : Level} (P : Poset ℓ ℓ)
         (𝓕 : Functor ((PosetCategory P) ^op) (CommRingsCategory {ℓ})) where

  open PosetStr (P .snd)

  -- an invertibility suprema of u ∈ P and a section s ∈ 𝓕(u) is
  -- a maximal element ≤ u where the restriction of s becomes invertible
  record IsInvSup (u : P .fst) (s : 𝓕 .F-ob u .fst) (𝓓ᵤs : P .fst) : Type ℓ where
    field
      𝓓≤ : 𝓓ᵤs ≤ u
      ≤𝓓ToInv : (v : P .fst) (v≤u : v ≤ u)
               → v ≤ 𝓓ᵤs → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob v) ˣ
      ≤𝓓FromInv : (v : P .fst) (v≤u : v ≤ u)
                 → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob v) ˣ → v ≤ 𝓓ᵤs

    𝓓Inv : 𝓕 .F-hom 𝓓≤ .fst s ∈ (𝓕 .F-ob (𝓓ᵤs)) ˣ
    𝓓Inv = ≤𝓓ToInv _ 𝓓≤ (is-refl _)

  unquoteDecl IsInvSupIsoΣ = declareRecordIsoΣ IsInvSupIsoΣ (quote IsInvSup)
  open IsInvSup

  isPropIsInvSup : ∀ u s 𝓓ᵤs → isProp (IsInvSup u s 𝓓ᵤs)
  isPropIsInvSup _ _ _ = isOfHLevelRetractFromIso 1 IsInvSupIsoΣ
                           (isProp×2 (is-prop-valued _ _)
                                     (isPropΠ3 (λ _ _ _ → ∈-isProp ((𝓕 .F-ob _) ˣ) _))
                                     (isPropΠ3 λ _ _ _ → is-prop-valued _ _))

  InvSup : (u : P .fst) (s : 𝓕 .F-ob u .fst) → Type ℓ
  InvSup u s = Σ[ 𝓓ᵤs ∈ P .fst ] IsInvSup u s 𝓓ᵤs

  -- invertibility suprema are unique (if they exist)
  isPropInvSup : ∀ u s → isProp (InvSup u s)
  isPropInvSup _ _ (_ , isInvSup𝓓) (_ , isInvSup𝓓') =
    Σ≡Prop (isPropIsInvSup _ _)
           (is-antisym _ _
             (isInvSup𝓓' .≤𝓓FromInv _ (isInvSup𝓓 .𝓓≤) (𝓓Inv isInvSup𝓓))
             (isInvSup𝓓 .≤𝓓FromInv _ (isInvSup𝓓' .𝓓≤) (𝓓Inv isInvSup𝓓')))

  IsInvMapAtStage : (u : P .fst) (𝓓ᵤ : 𝓕 .F-ob u .fst → P .fst) → Type ℓ
  IsInvMapAtStage u 𝓓ᵤ = ∀ s → IsInvSup u s (𝓓ᵤ s)

  isPropIsInvMapAtStage : ∀ u 𝓓ᵤ → isProp (IsInvMapAtStage u 𝓓ᵤ)
  isPropIsInvMapAtStage _ _ = isPropΠ (λ _ →  isPropIsInvSup _ _ _)

  InvMapAtStage : (u : P .fst) → Type ℓ
  InvMapAtStage u = Σ[ 𝓓ᵤ ∈ (𝓕 .F-ob u .fst → P .fst) ] IsInvMapAtStage u 𝓓ᵤ

  isPropInvMapAtStage : ∀ u → isProp (InvMapAtStage u)
  isPropInvMapAtStage u (𝓓ᵤ , isInvMapAtStageU𝓓ᵤ) (𝓓'ᵤ , isInvMapAtStageU𝓓'ᵤ) =
    Σ≡Prop (isPropIsInvMapAtStage u)
           (funExt (λ s → cong fst (isPropInvSup u s (𝓓ᵤ s , isInvMapAtStageU𝓓ᵤ s)
                                                     (𝓓'ᵤ s , isInvMapAtStageU𝓓'ᵤ s))))

  IsInvMap : (𝓓 : (u : P .fst) → 𝓕 .F-ob u .fst → P .fst) → Type ℓ
  IsInvMap 𝓓 = ∀ u → IsInvMapAtStage u (𝓓 u)

  isPropIsInvMap : ∀ 𝓓 → isProp (IsInvMap 𝓓)
  isPropIsInvMap 𝓓 = isPropΠ (λ _ → isPropIsInvMapAtStage _ _)

  InvMap = Σ[ 𝓓 ∈ ((u : P .fst) → 𝓕 .F-ob u .fst → P .fst) ] IsInvMap 𝓓

  -- invertibility maps are a property like structure
  isPropInvMap : isProp InvMap
  isPropInvMap (𝓓 , isInvMap𝓓) (𝓓' , isInvMap𝓓') =
    Σ≡Prop isPropIsInvMap
           (funExt (λ u → cong fst (isPropInvMapAtStage u (𝓓 u , isInvMap𝓓 u)
                                                          (𝓓' u , isInvMap𝓓' u))))


record LocRingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ


    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕

    𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst
    isSupport𝓓 : ∀ u → isSupport (𝓕 .F-ob u) L (𝓓 u)

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  field
    isInvMap𝓓 : IsInvMap IndPoset 𝓕 𝓓


record LocRingedLatticeHom (Y X : LocRingedLattice ℓ) : Type ℓ where
  open LocRingedLattice
  field
    π : DistLatticeHom (Y .L) (X .L)
    π♯ : NatTrans (Y .𝓕) ((X .𝓕) ∘F ((DistLatticeFunc (Y .L) (X .L) π) ^opF))
    pres𝓓 : {u : Y .L .fst} (s : Y .𝓕 .F-ob u .fst)
          → π .fst (Y .𝓓 u s) ≡ X .𝓓 (π .fst u) (π♯ .N-ob u .fst s)
