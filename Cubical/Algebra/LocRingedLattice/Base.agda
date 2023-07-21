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



-- locality on the stalks in terms of supports
module _ {ℓ : Level} (L : DistLattice ℓ)
         (𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})) where

  open Order (DistLattice→Lattice L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open PosetStr (IndPoset .snd) hiding (_≤_)

  -- an invertability suprema of u ∈ L and a section s ∈ 𝓕(u) is
  -- a maximal element ≤ u where the restriction of s becomes invertible
  record IsInvSup (u : L .fst) (s : 𝓕 .F-ob u .fst) (𝓓ᵤs : L .fst) : Type ℓ where
    field
      𝓓≤ : 𝓓ᵤs ≤ u
      ≤𝓓ToInv : (v : L .fst) (v≤u : v ≤ u)
               → v ≤ 𝓓ᵤs → 𝓕 .F-hom v≤u .fst s ∈ (𝓕 .F-ob v) ˣ
      ≤𝓓FromInv : (v : L .fst) (v≤u : v ≤ u)
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

  InvSup : (u : L .fst) (s : 𝓕 .F-ob u .fst) → Type ℓ
  InvSup u s = Σ[ 𝓓ᵤs ∈ L .fst ] IsInvSup u s 𝓓ᵤs

  -- invertibility suprema are unique (if they exist)
  isPropInvSup : ∀ u s → isProp (InvSup u s)
  isPropInvSup _ _ (_ , isInvSup𝓓) (_ , isInvSup𝓓') =
    Σ≡Prop (isPropIsInvSup _ _)
           (is-antisym _ _
             (isInvSup𝓓' .≤𝓓FromInv _ (isInvSup𝓓 .𝓓≤) (𝓓Inv isInvSup𝓓))
             (isInvSup𝓓 .≤𝓓FromInv _ (isInvSup𝓓' .𝓓≤) (𝓓Inv isInvSup𝓓')))

  IsInvMapAtStage : (u : L .fst) (𝓓ᵤ : 𝓕 .F-ob u .fst → L .fst) → Type ℓ
  IsInvMapAtStage u 𝓓ᵤ = ∀ s → IsInvSup u s (𝓓ᵤ s)

  isPropIsInvMapAtStage : ∀ u 𝓓ᵤ → isProp (IsInvMapAtStage u 𝓓ᵤ)
  isPropIsInvMapAtStage _ _ = isPropΠ (λ _ →  isPropIsInvSup _ _ _)

  InvMapAtStage : (u : L .fst) → Type ℓ
  InvMapAtStage u = Σ[ 𝓓ᵤ ∈ (𝓕 .F-ob u .fst → L .fst) ] IsInvMapAtStage u 𝓓ᵤ

  isPropInvMapAtStage : ∀ u → isProp (InvMapAtStage u)
  isPropInvMapAtStage u (𝓓ᵤ , isInvMapAtStageU𝓓ᵤ) (𝓓'ᵤ , isInvMapAtStageU𝓓'ᵤ) =
    Σ≡Prop (isPropIsInvMapAtStage u)
           (funExt (λ s → cong fst (isPropInvSup u s (𝓓ᵤ s , isInvMapAtStageU𝓓ᵤ s)
                                                     (𝓓'ᵤ s , isInvMapAtStageU𝓓'ᵤ s))))

  IsInvMap : (𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst) → Type ℓ
  IsInvMap 𝓓 = ∀ u → IsInvMapAtStage u (𝓓 u)

  isPropIsInvMap : ∀ 𝓓 → isProp (IsInvMap 𝓓)
  isPropIsInvMap 𝓓 = isPropΠ (λ _ → isPropIsInvMapAtStage _ _)

  InvMap = Σ[ 𝓓 ∈ ((u : L .fst) → 𝓕 .F-ob u .fst → L .fst) ] IsInvMap 𝓓

  -- invertibility maps are a property like structure
  isPropInvMap : isProp InvMap
  isPropInvMap (𝓓 , isInvMap𝓓) (𝓓' , isInvMap𝓓') =
    Σ≡Prop isPropIsInvMap
           (funExt (λ u → cong fst (isPropInvMapAtStage u (𝓓 u , isInvMap𝓓 u)
                                                          (𝓓' u , isInvMap𝓓' u))))

--     -- should probably be in properties
--     𝓓Pres≤ : (u v : L .fst) (s : 𝓕 .F-ob u .fst) (v≤u : v ≤ u)
--            → 𝓓 v (𝓕 .F-hom v≤u .fst s) ≤ 𝓓 u s
--     𝓓Pres≤ u v s v≤u = ≤𝓓FromInv _ _ _ (is-trans _ _ _ (𝓓≤ _ _) v≤u)
--                                         (subst (λ x → x ∈ (𝓕 .F-ob (𝓓 v (𝓕 .F-hom v≤u .fst s)) ˣ))
--                                           (sym (funExt⁻ (cong fst (𝓕 .F-seq _ _)) s))
--                                            (𝓓RestInv _ _))



record LocRingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ


    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕

    𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst
    isInvMap𝓓 : IsInvMap L 𝓕 𝓓
    isSupport𝓓 : ∀ u → isSupport (𝓕 .F-ob u) L (𝓓 u)

--   -- should probably be in properties
--   open DistLatticeStr (L .snd)
--   open Order (DistLattice→Lattice L)
--   open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
--   open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
--       using (∧lIsMin ; ∧≤RCancel ; ∧≤LCancel)
--   open PosetStr (IndPoset .snd) hiding (_≤_)

--   open IsInvSupport isInvSupport𝓓
--   open IsInvMap isInvMap𝓓

--   𝓓OfRest : (u v : L .fst) (s : 𝓕 .F-ob u .fst) (v≤u : v ≤ u)
--           → 𝓓 v (𝓕 .F-hom v≤u .fst s) ≡ v ∧l 𝓓 u s
--   𝓓OfRest u v s v≤u = is-antisym _ _ ltr rtl
--     where
--     ltr : 𝓓 v (𝓕 .F-hom v≤u .fst s) ≤ v ∧l 𝓓 u s
--     ltr = ≤m→≤j _ _ (∧lIsMin _ _ _ (≤j→≤m _ _ (𝓓≤ _ _))
--                                     (≤j→≤m _ _ (𝓓Pres≤ _ _ _ _)))

--     rtl : v ∧l 𝓓 u s ≤ 𝓓 v (𝓕 .F-hom v≤u .fst s)
--     rtl = ≤𝓓FromInv _ _ _ (≤m→≤j _ _ (∧≤RCancel _ _))
--            (subst (λ x → x ∈ ((𝓕 .F-ob _) ˣ)) s↿≡ (RingHomRespInv _ ⦃ 𝓓RestInv _ _ ⦄))
--       where
--       open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _}
--                              (𝓕 .F-hom (≤m→≤j _ _ (∧≤LCancel v (𝓓 u s))))
--       s↿v = 𝓕 .F-hom v≤u .fst s
--       s↿𝓓us =  𝓕 .F-hom (𝓓≤ u s) .fst s
--       s↿v↿v∧𝓓us = 𝓕 .F-hom (≤m→≤j _ _ (∧≤RCancel v (𝓓 u s))) .fst s↿v
--       s↿𝓓us↿v∧𝓓us = 𝓕 .F-hom (≤m→≤j _ _ (∧≤LCancel v (𝓓 u s))) .fst s↿𝓓us
--       s↿≡ : s↿𝓓us↿v∧𝓓us ≡ s↿v↿v∧𝓓us
--       s↿≡ = s↿𝓓us↿v∧𝓓us
--           ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s ⟩
--             𝓕 .F-hom (is-trans _ _ _ _ _) .fst s
--           ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (is-prop-valued _ _ _ _) ⟩
--             𝓕 .F-hom (is-trans _ _ _ (≤m→≤j _ _ (∧≤RCancel v (𝓓 u s))) v≤u) .fst s
--           ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq _ _)) s ⟩
--             s↿v↿v∧𝓓us ∎


record LocRingedLatticeHom (Y X : LocRingedLattice ℓ) : Type ℓ where
  open LocRingedLattice
  field
    π : DistLatticeHom (Y .L) (X .L)
    π♯ : NatTrans (Y .𝓕) ((X .𝓕) ∘F ((DistLatticeFunc (Y .L) (X .L) π) ^opF))
    pres𝓓 : {u : Y .L .fst} (s : Y .𝓕 .F-ob u .fst)
          → π .fst (Y .𝓓 u s) ≡ X .𝓓 (π .fst u) (π♯ .N-ob u .fst s)
