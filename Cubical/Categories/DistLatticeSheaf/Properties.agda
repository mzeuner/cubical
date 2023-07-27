{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
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

  open DistLatticeStr (snd L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open Join L
  open Order (DistLattice→Lattice L)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  open Category
  open Functor

  private
    Lᵒᵖ = (DistLatticeCategory L) ^op


  module _ {n : ℕ} (α : FinVec (L .fst) n)  (s : 𝓕 .F-ob (⋁ α) .fst) where

    private
      s↿ : (i : Fin n) → 𝓕 .F-ob (α i) .fst
      s↿ i = 𝓕 .F-hom (ind≤bigOp α i) .fst s

    invToRestInv⋁ : s ∈ 𝓕 .F-ob (⋁ α) ˣ
                  → ∀ i → s↿ i ∈ 𝓕 .F-ob (α i) ˣ
    invToRestInv⋁ sInv i = RingHomRespInv _ ⦃ sInv ⦄
      where
      open CommRingHomTheory {A' = 𝓕 .F-ob _} {B' = 𝓕 .F-ob _} (𝓕 .F-hom (ind≤bigOp α i))

    invFromRestInv⋁ : (∀ i → s↿ i ∈ 𝓕 .F-ob (α i) ˣ)
                    → s ∈ 𝓕 .F-ob (⋁ α) ˣ
    invFromRestInv⋁ s↿Inv = sInv
      where
      open isIso
      open Cone
      open LimCone (LimitsCommRingsCategory _ (𝓕 ∘F (FinVec→Diag L α)))
      𝓕⋁α≅lim𝓕∘α : Σ[ e ∈ CatIso CommRingsCategory (𝓕 .F-ob (⋁ α)) lim ]
                     isConeMor _ _ (e .fst)
      𝓕⋁α≅lim𝓕∘α = LimIso (𝓕 ∘F (FinVec→Diag L α))
                          (isDLSheafLimCone L _ 𝓕 isSheaf𝓕 _ α)
                          (LimitsCommRingsCategory _ (𝓕 ∘F (FinVec→Diag L α))) .fst

      -- names for readability
      φ : CommRingHom (𝓕 .F-ob (⋁ α)) lim
      φ = 𝓕⋁α≅lim𝓕∘α .fst .fst

      φ⁻¹ : CommRingHom lim (𝓕 .F-ob (⋁ α))
      φ⁻¹ = 𝓕⋁α≅lim𝓕∘α .fst .snd .inv

      φ⁻¹φ≡id = 𝓕⋁α≅lim𝓕∘α .fst .snd .ret

      φComm = 𝓕⋁α≅lim𝓕∘α .snd

      -- counterpart of s in (not definitionally) equal ring
      s' : lim .fst
      s' = φ .fst s

      s'↿ : (j : ob (DLShfDiag n ℓ)) → 𝓕 .F-ob ((FinVec→Diag L α) .F-ob j) .fst
      s'↿ j =  s' .coneOut j tt*

      s'Inv : s' ∈ lim ˣ
      s'Inv = invLimLemma (funcComp 𝓕 (FinVec→Diag L α)) s' s'↿Inv
        where
        s'↿Inv : ∀ j → s'↿ j ∈ 𝓕 .F-ob ((FinVec→Diag L α) .F-ob j) ˣ
        s'↿Inv (sing i) = subst (λ x → x ∈ 𝓕 .F-ob (α i) ˣ)
                                (funExt⁻ (cong fst (sym (φComm (sing i)))) s)
                                (s↿Inv i)
        s'↿Inv (pair i j i<j) =
          let open CommRingHomTheory (𝓕 .F-hom (FinVec→Diag L α .F-hom (singPairL {i<j = i<j}))) in
          subst (λ x → x ∈ 𝓕 .F-ob (α j ∧l α i) ˣ)
                (funExt⁻ (s' .coneOutCommutes singPairL) tt*)
                (RingHomRespInv _ ⦃ s'↿Inv (sing i) ⦄)

      sInv : s ∈ 𝓕 .F-ob (⋁ α) ˣ
      sInv = let open CommRingHomTheory φ⁻¹ in
             subst (λ x → x ∈ 𝓕 .F-ob (⋁ α) ˣ)
                   (funExt⁻ (cong fst φ⁻¹φ≡id) s)
                   (RingHomRespInv _ ⦃ s'Inv ⦄)



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
      where open CommRingHomTheory (𝓕 .F-hom (α≤u i))

    invFromRestInv : (∀ i → s↿ i ∈ 𝓕 .F-ob (α i) ˣ)
                   → s ∈ 𝓕 .F-ob u ˣ
    invFromRestInv s↿Inv = subst (λ x → x ∈ (𝓕 .F-ob u ˣ))
                                 s''≡s
                                 (RingHomRespInv _ ⦃ s'Inv ⦄)
      where
      ⋁α≤u : ⋁ α ≤ u
      ⋁α≤u = subst (λ x → ⋁ α ≤ x) ⋁α≡u (is-refl _)

      u≤⋁α : u ≤ ⋁ α
      u≤⋁α = subst (λ x → x ≤ ⋁ α) ⋁α≡u (is-refl _)

      open CommRingHomTheory (𝓕 .F-hom u≤⋁α)

      s' = 𝓕 .F-hom ⋁α≤u .fst s

      s'' = 𝓕 .F-hom u≤⋁α .fst s'

      s''≡s : s'' ≡ s
      s''≡s = s''
            ≡⟨ funExt⁻ (cong fst (sym (𝓕 .F-seq  ⋁α≤u u≤⋁α))) s ⟩
              𝓕 .F-hom (is-trans _ _ _ u≤⋁α ⋁α≤u) .fst s
            ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (is-prop-valued _ _ _ _) ⟩
              𝓕 .F-hom (is-refl _) .fst s
            ≡⟨ funExt⁻ (cong fst (𝓕 .F-id)) s ⟩
              s ∎

      s'↿ : (i : Fin n) → 𝓕 .F-ob (α i) .fst
      s'↿ i = 𝓕 .F-hom (ind≤bigOp α i) .fst s'

      s↿≡s'↿ : ∀ i → s↿ i ≡ s'↿ i
      s↿≡s'↿ i = 𝓕 .F-hom (α≤u i) .fst s
               ≡⟨ cong (λ x → 𝓕 .F-hom x .fst s) (is-prop-valued _ _ _ _) ⟩
                 𝓕 .F-hom (is-trans _ _ _ (ind≤bigOp α i) ⋁α≤u) .fst s
               ≡⟨ funExt⁻ (cong fst (𝓕 .F-seq  _ _)) s ⟩
                 𝓕 .F-hom (ind≤bigOp α i) .fst s' ∎

      s'Inv : s' ∈ 𝓕 .F-ob (⋁ α) ˣ
      s'Inv = invFromRestInv⋁ _ _
                λ i → subst (λ x → x ∈ 𝓕 .F-ob (α i) ˣ) (s↿≡s'↿ i) (s↿Inv i)
