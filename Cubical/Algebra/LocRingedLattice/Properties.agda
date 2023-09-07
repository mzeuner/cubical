{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

-- open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.DistLattice.Basis

open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Poset

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base
open import Cubical.Categories.DistLatticeSheaf.Properties

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

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
         (𝓓 : (u : P .fst) → 𝓕 .F-ob u .fst → PosetDownset.↓ P u)
         (isInvMap𝓓 : IsInvMap P 𝓕 𝓓) where

  open PosetStr (P .snd)
  open PosetDownset P
  open IsInvSup

  𝓓Pres≤ : (u : P .fst) (s : 𝓕 .F-ob u .fst) (v : P .fst) (v≤u : v ≤ u)
         → 𝓓 v (𝓕 .F-hom v≤u .fst s) .fst  ≤ 𝓓 u s .fst
  𝓓Pres≤ u s v v≤u = isInvMap𝓓 u s .≤𝓓FromInv _
                       (is-trans _ _ _ (𝓓 v (𝓕 .F-hom v≤u .fst s) .snd) v≤u)
                         (subst (λ x → x ∈ (𝓕 .F-ob (𝓓 v (𝓕 .F-hom v≤u .fst s) .fst) ˣ))
                           (sym (funExt⁻ (cong fst (𝓕 .F-seq _ _)) s))
                             (𝓓Inv (isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s))))

  ≡𝓓FromInv : (u : P .fst) (s : 𝓕 .F-ob u .fst)
            → s ∈ (𝓕 .F-ob u) ˣ → u ≡ 𝓓 u s .fst
  ≡𝓓FromInv u s sInv = is-antisym _ _ (isInvMap𝓓 u s .≤𝓓FromInv _ (is-refl _)
                                        (subst (λ x → x ∈ 𝓕 .F-ob u ˣ)
                                               (sym (funExt⁻ (cong fst (𝓕 .F-id)) s)) sInv))
                                      (𝓓 u s .snd)

  ≡𝓓ToInv : (u : P .fst) (s : 𝓕 .F-ob u .fst)
          → u ≡ 𝓓 u s .fst → s ∈ (𝓕 .F-ob u) ˣ
  ≡𝓓ToInv u s u≡𝓓ᵤs = subst (λ x → x ∈ 𝓕 .F-ob u ˣ)
                            (funExt⁻ (cong fst (𝓕 .F-id)) s)
                            (isInvMap𝓓 u s .≤𝓓ToInv u (is-refl _) (subst (u ≤_) u≡𝓓ᵤs (is-refl _)))


-- InvSup porperties in a meet semilattice
module MeetSemilatticeInvSupTheory (M' : Semilattice ℓ) where

  open MeetSemilattice M'
  open SemilatticeStr (snd M') renaming (_·_ to _∧l_ ; ε to 1l ; ·Assoc to ∧Assoc)
  open CommMonoidTheory (Semilattice→CommMonoid M')
  open PosetStr (IndPoset .snd) hiding (_≤_)
  open PosetDownset IndPoset
  private M = fst M'

  open Functor
  module _ (𝓕 : Functor (PosetCategory IndPoset ^op) (CommRingsCategory {ℓ}))
           (𝓓 : (u : M) → 𝓕 .F-ob u .fst → ↓ u)
           (isInvMap𝓓 : IsInvMap IndPoset 𝓕 𝓓) where

    open PosetInvSupTheory IndPoset 𝓕 𝓓 isInvMap𝓓
    open IsInvSup

    𝓓OfRest : (u : M) (s : 𝓕 .F-ob u .fst) (v : M) (v≤u : v ≤ u)
            → 𝓓 v (𝓕 .F-hom v≤u .fst s) .fst ≡ v ∧l 𝓓 u s .fst
    𝓓OfRest u s v v≤u = is-antisym _ _ l≤r r≤l
      where
      l≤r : 𝓓 v (𝓕 .F-hom v≤u .fst s) .fst ≤ v ∧l 𝓓 u s .fst
      l≤r = ∧lIsMin _ _ _ (𝓓 v (𝓕 .F-hom v≤u .fst s) .snd) (𝓓Pres≤ _ _ _ _)

      r≤l : v ∧l 𝓓 u s .fst ≤ 𝓓 v (𝓕 .F-hom v≤u .fst s) .fst
      r≤l = isInvMap𝓓 v (𝓕 .F-hom v≤u .fst s) .≤𝓓FromInv _ (∧≤RCancel _ _)
        (subst (λ x → x ∈ 𝓕 .F-ob _ ˣ) s↿≡ (RingHomRespInv _ ⦃ 𝓓Inv (isInvMap𝓓 _ _) ⦄))
        where
        open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _}
                               (𝓕 .F-hom (∧≤LCancel v (𝓓 u s .fst)))
        s↿v = 𝓕 .F-hom v≤u .fst s
        s↿𝓓us = 𝓕 .F-hom (𝓓 u s .snd)  .fst s
        s↿v↿v∧𝓓us = 𝓕 .F-hom (∧≤RCancel v (𝓓 u s .fst)) .fst s↿v
        s↿𝓓us↿v∧𝓓us = 𝓕 .F-hom (∧≤LCancel v (𝓓 u s .fst)) .fst s↿𝓓us
        s↿≡ : s↿𝓓us↿v∧𝓓us ≡ s↿v↿v∧𝓓us
        s↿≡ = s↿𝓓us↿v∧𝓓us
            ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s ⟩
              𝓕 .F-hom (is-trans _ _ _ _ _) .fst s
            ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (is-prop-valued _ _ _ _) ⟩
              𝓕 .F-hom (is-trans _ _ _ (∧≤RCancel v (𝓓 u s .fst)) v≤u) .fst s
            ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq _ _)) s ⟩
              s↿v↿v∧𝓓us ∎

    𝓓OfRest∧ : (u : M) (s : 𝓕 .F-ob u .fst) (v : M)
             → 𝓓 (v ∧l u) (𝓕 .F-hom (∧≤LCancel _ _) .fst s) .fst ≡ v ∧l 𝓓 u s .fst
    𝓓OfRest∧ u s v =
      𝓓 (v ∧l u) (𝓕 .F-hom (∧≤LCancel _ _) .fst s) .fst ≡⟨ 𝓓OfRest u s (v ∧l u) (∧≤LCancel _ _) ⟩
      v ∧l u ∧l 𝓓 u s .fst ≡⟨ commAssocr _ _ _ ⟩
      v ∧l 𝓓 u s .fst ∧l u ≡⟨ sym (∧Assoc _ _ _) ⟩
      v ∧l (𝓓 u s .fst  ∧l u) ≡⟨ cong (v ∧l_) (𝓓 u s .snd) ⟩
      v ∧l 𝓓 u s .fst ∎


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
  open PosetDownset
  open DistLatticeStr ⦃...⦄
  private instance _ = L' .snd

  open Functor
  open RingedLatticeTheory L' 𝓕 isSheaf𝓕

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

  private 𝓕ᴮ = 𝓕 ∘F (B↪L ^opF)

  module _ (𝓓ᴮ : (u : B) → 𝓕ᴮ .F-ob u .fst → ↓ BPoset u)
           (isInvMap𝓓ᴮ : IsInvMap BPoset 𝓕ᴮ 𝓓ᴮ) where
--            (pres1𝓓ᴮ : ∀ u →  𝓓ᴮ u (𝓕 .F-ob (u .fst) .snd .CommRingStr.1r) .fst ≡ 1l)
--            (pres0𝓓ᴮ : ∀ u →  𝓓ᴮ u (𝓕 .F-ob (u .fst) .snd .CommRingStr.0r) .fst ≡ 0l)
--            (·≡∧𝓓ᴮ : ∀ u x y → 𝓓ᴮ u (𝓕 .F-ob (u .fst) .snd .CommRingStr._·_ x y) .fst
--                             ≡ 𝓓ᴮ u x .fst ∧l 𝓓ᴮ u y .fst)
--            (+≤∨𝓓ᴮ : ∀ u x y → 𝓓ᴮ u (𝓕 .F-ob (u .fst) .snd .CommRingStr._+_ x y) .fst
--                             ≤ 𝓓ᴮ u x .fst ∨l 𝓓ᴮ u y .fst) where


    open IsBasis ⦃...⦄
    private instance _ = isBasisB
    open PosetStr (LPoset .snd) hiding (_≤_ ; is-prop-valued)

    InvMapFromBasisStage : (u : L) → InvMapAtStage LPoset 𝓕 u
-- Σ[ 𝓓 ∈ InvMapAtStage LPoset 𝓕 u ] isSupport (𝓕 .F-ob u) L' (𝓓 .fst)
    InvMapFromBasisStage u = PT.rec (isPropInvMapAtStage _ _ _)
                                      uHelperΣ
                                        (⋁Basis u)
      where
      uHelperΣ : Σ[ n ∈ ℕ ] Σ[ α ∈ FinVec L n ] (∀ i → α i ∈ B') × (⋁ α ≡ u)
              → InvMapAtStage LPoset 𝓕 u
-- Σ[ 𝓓 ∈ InvMapAtStage LPoset 𝓕 u ] isSupport (𝓕 .F-ob u) L' (𝓓 .fst)
      uHelperΣ (n , α , α∈B , ⋁α≡u) = 𝓓ᵤ , isInvMapAtStage𝓓ᵤ
        where
        α≤u : ∀ i → α i ≤ u
        α≤u i = subst (λ x → α i ≤ x) ⋁α≡u (ind≤⋁ α i)

        𝓓ᵤ : 𝓕 .F-ob u .fst → ↓ LPoset u
        𝓓ᵤ s = (⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst .fst)
             , ⋁IsMax _ u λ i → is-trans _ _ _
                                  (B↪L .F-hom (𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .snd))
                                  (α≤u i)


        ≤𝓓ToInvB : ∀ (s : 𝓕 .F-ob u .fst) (v : B) (v≤u : v .fst ≤ u)
                 → v .fst ≤ 𝓓ᵤ s .fst → 𝓕 .F-hom v≤u .fst s ∈ 𝓕 .F-ob (v .fst) ˣ
        ≤𝓓ToInvB s (v , v∈B) v≤u v≤𝓓ᵤs =
          invFromRestInv v s↿v 𝓓ᴮ[s↿v↿v∧α] ⋁𝓓ᴮ[s↿v↿v∧α]≡v
            λ i → subst (λ x → x ∈ 𝓕 .F-ob (𝓓ᴮ[s↿v↿v∧α] i) ˣ)
                  (funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s↿v
                    ∙ cong (λ x → 𝓕 .F-hom x .fst s↿v)
                           (LPoset .snd .is-prop-valued _ _ _ _))
                  (𝓓Inv (isInvMap𝓓ᴮ ((v , v∈B) ∧b (α i , α∈B i)) (s↿v↿v∧α i)))
          where
          open MeetSemilattice (Basis→MeetSemilattice L' B' isBasisB) renaming (_≤_ to _≤b_) hiding (IndPoset)
          open SemilatticeStr ((Basis→MeetSemilattice L' B' isBasisB) .snd) renaming (_·_ to _∧b_)
          open IsInvSup
          open MeetSemilatticeInvSupTheory (Basis→MeetSemilattice L' B' isBasisB)

          v∧α≤α : ∀ i → (v , v∈B) ∧b (α i , α∈B i) ≤b (α i , α∈B i)
          v∧α≤α i = ∧≤LCancel _ _

          v∧α≤v : ∀ i → (v , v∈B) ∧b (α i , α∈B i) ≤b (v , v∈B)
          v∧α≤v i = ∧≤RCancel _ _

          s↿v = 𝓕 .F-hom v≤u .fst s

          s↿α : (i : Fin n) → 𝓕 .F-ob (α i) .fst
          s↿α i = 𝓕 .F-hom (α≤u i) .fst s

          s↿α↿v∧α : (i : Fin n) → 𝓕 .F-ob (v ∧l α i) .fst
          s↿α↿v∧α i = 𝓕 .F-hom (B↪L .F-hom (v∧α≤α i)) .fst (s↿α i)

          s↿v↿v∧α : (i : Fin n) → 𝓕 .F-ob (v ∧l α i) .fst
          s↿v↿v∧α i = 𝓕 .F-hom (B↪L .F-hom (v∧α≤v i)) .fst s↿v

          𝓓ᴮ[s↿α] : FinVec L n
          𝓓ᴮ[s↿α] i = 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst .fst

          𝓓ᴮ[s↿v↿v∧α] : FinVec L n
          𝓓ᴮ[s↿v↿v∧α] i = 𝓓ᴮ ((v , v∈B) ∧b (α i , α∈B i)) (s↿v↿v∧α i) .fst .fst

          𝓓ᴮ≡ : ∀ i →  𝓓ᴮ[s↿v↿v∧α] i ≡ v ∧l 𝓓ᴮ[s↿α] i
          𝓓ᴮ≡ i =
              cong (λ x → 𝓓ᴮ ((v , v∈B) ∧b (α i , α∈B i)) x .fst .fst) s↿≡
            ∙ cong fst (𝓓OfRest∧ 𝓕ᴮ 𝓓ᴮ isInvMap𝓓ᴮ  (α i , α∈B i) (s↿α i) (v , v∈B))
            where
            s↿≡ : s↿v↿v∧α i ≡ s↿α↿v∧α i
            s↿≡ = s↿v↿v∧α i
                ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s ⟩
                  𝓕 .F-hom (is-trans _ _ _ _ _) .fst s
                ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (LPoset .snd .is-prop-valued _ _ _ _) ⟩
                  𝓕 .F-hom (is-trans _ _ _ ((B↪L .F-hom (v∧α≤α i))) (α≤u i)) .fst s
                ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq _ _)) s ⟩
                  s↿α↿v∧α i ∎

          ⋁𝓓ᴮ[s↿v↿v∧α]≡v : ⋁ 𝓓ᴮ[s↿v↿v∧α] ≡ v
          ⋁𝓓ᴮ[s↿v↿v∧α]≡v = ⋁Ext 𝓓ᴮ≡ ∙∙ sym (⋁Meetrdist v 𝓓ᴮ[s↿α]) ∙∙ ≤j→≤m _ _ v≤𝓓ᵤs


        ≤𝓓FromInvB : ∀ (s : 𝓕 .F-ob u .fst) (v : B) (v≤u : v .fst ≤ u)
                   → 𝓕 .F-hom v≤u .fst s ∈ 𝓕 .F-ob (v .fst) ˣ → v .fst ≤ 𝓓ᵤ s .fst
        ≤𝓓FromInvB s (v , v∈B) v≤u s↿vInv =
          subst (λ x → x ≤ 𝓓ᵤ s .fst) ⋁v∧α≡v (≤-⋁Ext _ _ v∧α≤𝓓ᴮs↿α)
          where
          open MeetSemilattice (Basis→MeetSemilattice L' B' isBasisB) renaming (_≤_ to _≤b_) hiding (IndPoset)
          open SemilatticeStr ((Basis→MeetSemilattice L' B' isBasisB) .snd) renaming (_·_ to _∧b_)
          open IsInvSup

          v∧α≤α : ∀ i → (v , v∈B) ∧b (α i , α∈B i) ≤b (α i , α∈B i)
          v∧α≤α i = ∧≤LCancel _ _

          v∧α≤v : ∀ i → (v , v∈B) ∧b (α i , α∈B i) ≤b (v , v∈B)
          v∧α≤v i = ∧≤RCancel _ _

          s↿α : (i : Fin n) → 𝓕 .F-ob (α i) .fst
          s↿α i = 𝓕 .F-hom (α≤u i) .fst s

          s↿v = 𝓕 .F-hom v≤u .fst s

          s↿v↿v∧α : (i : Fin n) → 𝓕 .F-ob (v ∧l α i) .fst
          s↿v↿v∧α i = 𝓕 .F-hom (B↪L .F-hom (v∧α≤v i)) .fst s↿v

          s↿α↿v∧α : (i : Fin n) → 𝓕 .F-ob (v ∧l α i) .fst
          s↿α↿v∧α i = 𝓕 .F-hom (B↪L .F-hom (v∧α≤α i)) .fst (s↿α i)

          s↿α↿v∧αInv : ∀ i → s↿α↿v∧α i ∈ 𝓕 .F-ob (v ∧l α i) ˣ
          s↿α↿v∧αInv i =
            subst (λ x → x ∈ (𝓕 .F-ob (v ∧l α i) ˣ)) s↿≡ (RingHomRespInv _ ⦃ s↿vInv ⦄)
            where
            open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _}
                                   (𝓕 .F-hom (B↪L .F-hom (v∧α≤v i)))
            s↿≡ : s↿v↿v∧α i ≡ s↿α↿v∧α i
            s↿≡ = s↿v↿v∧α i
                ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s ⟩
                  𝓕 .F-hom (is-trans _ _ _ _ _) .fst s
                ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (LPoset .snd .is-prop-valued _ _ _ _) ⟩
                  𝓕 .F-hom (is-trans _ _ _ ((B↪L .F-hom (v∧α≤α i))) (α≤u i)) .fst s
                ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq _ _)) s ⟩
                  s↿α↿v∧α i ∎



          v∧α≤𝓓ᴮs↿α : ∀ i → v ∧l α i ≤ 𝓓ᴮ (α i , α∈B i) (s↿α i) .fst .fst
          v∧α≤𝓓ᴮs↿α i = B↪L .F-hom (isInvMap𝓓ᴮ (α i , α∈B i) (s↿α i)
                                      .≤𝓓FromInv _ (v∧α≤α i) (s↿α↿v∧αInv i))

          ⋁v∧α≡v : ⋁ (λ i → v ∧l α i) ≡ v
          ⋁v∧α≡v = sym (⋁Meetrdist v α) ∙∙ cong (v ∧l_) (⋁α≡u) ∙∙ ≤j→≤m _ _ v≤u



        open IsInvSup
        isInvMapAtStage𝓓ᵤ : ∀ s → IsInvSup LPoset 𝓕 _ _ (𝓓ᵤ s)

        ≤𝓓ToInv (isInvMapAtStage𝓓ᵤ s) v =
          PT.rec (isPropΠ2 (λ _ _ → ∈-isProp (𝓕 .F-ob v ˣ) _)) vHelperΣ (⋁Basis v)
          where
          vHelperΣ : Σ[ m ∈ ℕ ] Σ[ β ∈ FinVec L m ] (∀ i → β i ∈ B') × (⋁ β ≡ v)
                   → (v≤u : v ≤ u) → v ≤ 𝓓ᵤ s .fst → 𝓕 .F-hom v≤u .fst s ∈ 𝓕 .F-ob v ˣ
          vHelperΣ (m , β , β∈B , ⋁β≡v) v≤u v≤𝓓ᵤs =
            invFromRestInv v s↿v β ⋁β≡v s↿v↿βInv
            where
            β≤v : ∀ i → β i ≤ v
            β≤v i = subst (λ x → β i ≤ x) ⋁β≡v (ind≤⋁ β i)

            s↿v = 𝓕 .F-hom v≤u .fst s

            s↿v↿β : (i : Fin m) → 𝓕 .F-ob (β i) .fst
            s↿v↿β i = 𝓕 .F-hom (β≤v i) .fst s↿v

            s↿v↿βInv : ∀ i → s↿v↿β i ∈ 𝓕 .F-ob (β i) ˣ
            s↿v↿βInv i = subst (λ x → x ∈ 𝓕 .F-ob (β i) ˣ)
                              (funExt⁻ (cong fst (𝓕 .F-seq _ _)) s)
                              (≤𝓓ToInvB s (β i , β∈B i) βᵢ≤u βᵢ≤𝓓ᵤs)
              where
              βᵢ≤u : β i ≤ u
              βᵢ≤u = is-trans _ _ _ (β≤v i) v≤u

              βᵢ≤𝓓ᵤs : β i ≤ 𝓓ᵤ s .fst
              βᵢ≤𝓓ᵤs = is-trans _ _ _ (β≤v i) v≤𝓓ᵤs

        ≤𝓓FromInv (isInvMapAtStage𝓓ᵤ s) v =
          PT.rec (isPropΠ2 (λ _ _ → LPoset .snd .is-prop-valued _ _)) vHelperΣ (⋁Basis v)
          where
          vHelperΣ : Σ[ m ∈ ℕ ] Σ[ β ∈ FinVec L m ] (∀ i → β i ∈ B') × (⋁ β ≡ v)
                   → (v≤u : v ≤ u) → 𝓕 .F-hom v≤u .fst s ∈ 𝓕 .F-ob v ˣ → v ≤ 𝓓ᵤ s .fst
          vHelperΣ (m , β , β∈B , ⋁β≡v) v≤u s↿vInv =
            subst (λ x → x ≤ 𝓓ᵤ s .fst) ⋁β≡v (⋁IsMax β (𝓓ᵤ s .fst) β≤𝓓ᵤs)
            where
            β≤v : ∀ i → β i ≤ v
            β≤v i = subst (λ x → β i ≤ x) ⋁β≡v (ind≤⋁ β i)

            β≤𝓓ᵤs : ∀ i → β i ≤ 𝓓ᵤ s .fst
            β≤𝓓ᵤs i = ≤𝓓FromInvB s (β i , β∈B i) βᵢ≤u (subst (λ x → x ∈ 𝓕 .F-ob (β i) ˣ)
                                                        (funExt⁻ (cong fst (sym (𝓕 .F-seq _ _))) s)
                                                        s↿v↿βᵢInv)
              where
              open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _} (𝓕 .F-hom (β≤v i))
              βᵢ≤u : β i ≤ u
              βᵢ≤u = is-trans _ _ _ (β≤v i) v≤u

              s↿v = 𝓕 .F-hom v≤u .fst s
              s↿v↿βᵢ = 𝓕 .F-hom (β≤v i) .fst s↿v

              s↿v↿βᵢInv : s↿v↿βᵢ ∈ 𝓕 .F-ob (β i) ˣ
              s↿v↿βᵢInv = RingHomRespInv _ ⦃ s↿vInv ⦄

--         open isSupport
--         open IsRingHom
--         open CommRingStr ⦃...⦄
--         private instance _ = (𝓕 .F-ob u .snd)
--         isSupport𝓓ᵤ : isSupport (𝓕 .F-ob u) L' 𝓓ᵤ
--         pres0 isSupport𝓓ᵤ =
--             (⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst 0r) .fst)
--           ≡⟨ ⋁Ext (λ i → cong (λ s → 𝓓ᴮ (α i , α∈B i) s .fst) (𝓕 .F-hom (α≤u i) .snd .pres0)) ⟩
--             (⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-ob (α i) .snd .0r) .fst)
--           ≡⟨ ⋁Ext (λ i → pres0𝓓ᴮ (α i , α∈B i)) ⟩
--             (⋁ {n = n} λ _ → 0l)
--           ≡⟨ ⋁0l n ⟩
--             0l ∎

--         pres1 isSupport𝓓ᵤ = {!!} -- with (n == 0)
--         -- ... | true = ?
--         -- ... | false = ?
--           where
--           path : 𝓓ᵤ 1r ≡ ⋁ {n = n} λ _ → 1l -- 𝓓ᵤ 1 = u!!!!!!!!!!!!!!!
--           path = ⋁Ext (λ i → cong (λ s → 𝓓ᴮ (α i , α∈B i) s .fst) (𝓕 .F-hom (α≤u i) .snd .pres1))
--                ∙ ⋁Ext (λ i → pres1𝓓ᴮ (α i , α∈B i))
--           -- need case distinction:
--           -- if n = 0 ⇒ 1=0 in L
--           -- else: ⋁1l

--         ·≡∧ isSupport𝓓ᵤ s t = {!!}
--           --   (⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst (s · t)) .fst)
--           -- ≡⟨ {!!} ⟩
--           --   (⋁ λ i → 𝓓ᴮ (α i , α∈B i)
--           --                (𝓕 .F-ob (α i) .snd ._·_ (𝓕 .F-hom (α≤u i) .fst s)
--           --                                          (𝓕 .F-hom (α≤u i) .fst t)) .fst)
--           -- ≡⟨ {!!} ⟩
--           --   (⋁ λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst
--           --         ∧l 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst t) .fst)
--           -- ≡⟨ {!!} ⟩ --this is not a general lemma
--           --   𝓓ᵤ s ∧l 𝓓ᵤ t ∎

--         +≤∨ isSupport𝓓ᵤ s t =
--           subst2 (_≤_)
--                  (sym (⋁Ext (λ i → cong (λ x → 𝓓ᴮ (α i , α∈B i) x .fst) (𝓕 .F-hom (α≤u i) .snd .pres+ s t))))
--                  (⋁Split (λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) .fst)
--                           (λ i → 𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst t) .fst))
--                  (≤-⋁Ext _ _ λ i → +≤∨𝓓ᴮ (α i , α∈B i) (𝓕 .F-hom (α≤u i) .fst s) (𝓕 .F-hom (α≤u i) .fst t))


    InvMapFromBasis : InvMap LPoset 𝓕
    InvMapFromBasis = InvMapAtStage→InvMap _ _ InvMapFromBasisStage
