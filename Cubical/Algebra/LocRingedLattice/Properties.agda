{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

-- open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.HITs.PropositionalTruncation as PT

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
open import Cubical.Categories.Instances.Poset

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


-- InvSup porperties in arbitrary posets
module PosetInvSupTheory {ℓ : Level} (P : Poset ℓ ℓ)
         (𝓕 : Functor ((PosetCategory P) ^op) (CommRingsCategory {ℓ}))
         (𝓓 : (u : P .fst) → 𝓕 .F-ob u .fst → P .fst)
         (isInvMap𝓓 : IsInvMap P 𝓕 𝓓) where

  open PosetStr (P .snd)
  open IsInvSup

  𝓓Pres≤ : (u : P .fst) (s : 𝓕 .F-ob u .fst) (v : P .fst) (v≤u : v ≤ u)
         → 𝓓 v (𝓕 .F-hom v≤u .fst s) ≤ 𝓓 u s
  𝓓Pres≤ u s v v≤u = isInvMap𝓓 u s .≤𝓓FromInv _
                       (is-trans _ _ _ (isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s) .𝓓≤) v≤u)
                         (subst (λ x → x ∈ (𝓕 .F-ob (𝓓 v (𝓕 .F-hom v≤u .fst s)) ˣ))
                           (sym (funExt⁻ (cong fst (𝓕 .F-seq _ _)) s))
                             (𝓓Inv (isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s))))

  ≡𝓓FromInv : (u : P .fst) (s : 𝓕 .F-ob u .fst)
            → s ∈ (𝓕 .F-ob u) ˣ → u ≡ 𝓓 u s
  ≡𝓓FromInv u s sInv = is-antisym _ _ (isInvMap𝓓 u s .≤𝓓FromInv _ (is-refl _)
                                        (subst (λ x → x ∈ 𝓕 .F-ob u ˣ)
                                               (sym (funExt⁻ (cong fst (𝓕 .F-id)) s)) sInv))
                                      (isInvMap𝓓 u s .𝓓≤)

  ≡𝓓ToInv : (u : P .fst) (s : 𝓕 .F-ob u .fst)
          → u ≡ 𝓓 u s → s ∈ (𝓕 .F-ob u) ˣ
  ≡𝓓ToInv u s u≡𝓓ᵤs = subst (λ x → x ∈ 𝓕 .F-ob u ˣ)
                            (funExt⁻ (cong fst (𝓕 .F-id)) s)
                            (isInvMap𝓓 u s .≤𝓓ToInv u (is-refl _) (subst (u ≤_) u≡𝓓ᵤs (is-refl _)))


-- InvSup porperties in a meet semilattice
module MeetSemilatticeInvSupTheory (M' : Semilattice ℓ) where

  open MeetSemilattice M'
  open SemilatticeStr (snd M') renaming (_·_ to _∧l_ ; ε to 1l ; ·Assoc to ∧Assoc)
  open CommMonoidTheory (Semilattice→CommMonoid M')
  open PosetStr (IndPoset .snd) hiding (_≤_)
  private M = fst M'

  open Functor
  module _ (𝓕 : Functor (PosetCategory IndPoset ^op) (CommRingsCategory {ℓ}))
           (𝓓 : (u : M) → 𝓕 .F-ob u .fst → M)
           (isInvMap𝓓 : IsInvMap IndPoset 𝓕 𝓓) where

    open PosetInvSupTheory IndPoset 𝓕 𝓓 isInvMap𝓓
    open IsInvSup

    𝓓OfRest : (u : M) (s : 𝓕 .F-ob u .fst) (v : M) (v≤u : v ≤ u)
            → 𝓓 v (𝓕 .F-hom v≤u .fst s) ≡ v ∧l 𝓓 u s
    𝓓OfRest u s v v≤u = is-antisym _ _ l≤r r≤l
      where
      l≤r : 𝓓 v (𝓕 .F-hom v≤u .fst s) ≤ v ∧l 𝓓 u s
      l≤r = ∧lIsMin _ _ _ (isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s) .𝓓≤) (𝓓Pres≤ _ _ _ _)

      r≤l : v ∧l 𝓓 u s ≤ 𝓓 v (𝓕 .F-hom v≤u .fst s)
      r≤l = isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s) .≤𝓓FromInv _ (∧≤RCancel _ _)
        (subst (λ x → x ∈ 𝓕 .F-ob _ ˣ) s↿≡ (RingHomRespInv _ ⦃ 𝓓Inv (isInvMap𝓓 _ _) ⦄))
        where
        open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _}
                               (𝓕 .F-hom (∧≤LCancel v (𝓓 u s)))
        s↿v = 𝓕 .F-hom v≤u .fst s
        s↿𝓓us = 𝓕 .F-hom (isInvMap𝓓 u s .𝓓≤)  .fst s
        s↿v↿v∧𝓓us = 𝓕 .F-hom (∧≤RCancel v (𝓓 u s)) .fst s↿v
        s↿𝓓us↿v∧𝓓us = 𝓕 .F-hom (∧≤LCancel v (𝓓 u s)) .fst s↿𝓓us
        s↿≡ : s↿𝓓us↿v∧𝓓us ≡ s↿v↿v∧𝓓us
        s↿≡ = s↿𝓓us↿v∧𝓓us
            ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s ⟩
              𝓕 .F-hom (is-trans _ _ _ _ _) .fst s
            ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (is-prop-valued _ _ _ _) ⟩
              𝓕 .F-hom (is-trans _ _ _ (∧≤RCancel v (𝓓 u s)) v≤u) .fst s
            ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq _ _)) s ⟩
              s↿v↿v∧𝓓us ∎

    𝓓OfRest∧ : (u : M) (s : 𝓕 .F-ob u .fst) (v : M)
             → 𝓓 (u ∧l v) (𝓕 .F-hom (∧≤RCancel _ _) .fst s) ≡ v ∧l 𝓓 u s
    𝓓OfRest∧ u s v =
      𝓓 (u ∧l v) (𝓕 .F-hom (∧≤RCancel _ _) .fst s) ≡⟨ 𝓓OfRest u s (u ∧l v) (∧≤RCancel _ _) ⟩
      u ∧l v ∧l 𝓓 u s ≡⟨ commAssocr3 _ _ _ ⟩
      v ∧l 𝓓 u s ∧l u ≡⟨ sym (∧Assoc _ _ _) ⟩
      v ∧l (𝓓 u s ∧l u) ≡⟨ cong (v ∧l_) (isInvMap𝓓 u s .𝓓≤) ⟩
      v ∧l 𝓓 u s ∎


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
  open Order (DistLattice→Lattice L')
  open PosetStr using (is-prop-valued)

  open Functor

  private
    L = fst L'
    B = Σ[ u ∈ L ] (u ∈ B')

    LPoset = JoinSemilattice.IndPoset (Lattice→JoinSemilattice (DistLattice→Lattice L'))
    BPoset = MeetSemilattice.IndPoset (Basis→MeetSemilattice L' B' isBasisB)

    B↪L : Functor (PosetCategory BPoset) (PosetCategory LPoset)
    F-ob B↪L = fst
    F-hom B↪L {x} {y} x≤y = ≤m→≤j (fst x) (fst y) (cong fst x≤y)
    F-id B↪L = LPoset .snd .is-prop-valued _ _ _ _
    F-seq B↪L _ _ = LPoset .snd .is-prop-valued _ _ _ _

    𝓕ᴮ = 𝓕 ∘F (B↪L ^opF)

  module _ (𝓓ᴮ : (u : B) → 𝓕ᴮ .F-ob u .fst → B) (isInvMap𝓓ᴮ : IsInvMap BPoset 𝓕ᴮ 𝓓ᴮ) where

    open IsBasis isBasisB
    open PosetStr (LPoset .snd) hiding (_≤_)

    InvMapFromBasisStage : (u : L) → InvMapAtStage LPoset 𝓕 u
    InvMapFromBasisStage u = PT.rec (isPropInvMapAtStage LPoset 𝓕 u) helperΣ (⋁Basis u)
      where
      helperΣ : Σ[ n ∈ ℕ ] Σ[ α ∈ FinVec L n ] (∀ i → α i ∈ B') × (⋁ α ≡ u)
              → InvMapAtStage LPoset 𝓕 u
      helperΣ (n , α , α∈B , ⋁α≡u) = 𝓓ᵤ , isInvMapAtStage𝓓ᵤ
        where
        α≤u : ∀ i → α i ≤ u
        α≤u i = subst (λ x → α i ≤ x) ⋁α≡u (ind≤bigOp α i)

        𝓓ᵤ : 𝓕 .F-ob u .fst → L
        𝓓ᵤ s = ⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst

        open IsInvSup
        isInvMapAtStage𝓓ᵤ : ∀ s → IsInvSup LPoset 𝓕 _ _ (𝓓ᵤ s)
        𝓓≤ (isInvMapAtStage𝓓ᵤ s) = bigOpIsMax _ u
          λ i → is-trans _ _ _
                  (B↪L .F-hom (isInvMap𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .𝓓≤))
                  (α≤u i)
        ≤𝓓ToInv (isInvMapAtStage𝓓ᵤ s) = {!!}
        ≤𝓓FromInv (isInvMapAtStage𝓓ᵤ s) = {!!}
