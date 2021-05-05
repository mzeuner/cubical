{-# OPTIONS --cubical --safe --no-import-sorts --experimental-lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Localisation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra hiding (⟨_⟩a)
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT


private
  variable
    ℓ ℓ′ : Level



module AlgLoc (R' : CommRing {ℓ})
              (S' : ℙ (fst R')) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = fst R'
 open CommAlgebra
 open AlgebraHom
 open CommRingStr (snd R') renaming (_+_ to _+r_ ; _·_ to _·r_ ; ·Rid to ·rRid)
 open Theory (CommRing→Ring R')
 open CommTheory R'
 open Loc R' S' SMultClosedSubset
 open S⁻¹RUniversalProp R' S' SMultClosedSubset
 open CommAlgChar R'

 S⁻¹RAsCommAlg : CommAlgebra R'
 S⁻¹RAsCommAlg = toCommAlg (S⁻¹RAsCommRing , /1AsCommRingHom)


 hasLocAlgUniversalProp : (A : CommAlgebra R')
                        → (∀ s → s ∈ S' → _⋆_ A s (1a A) ∈ (CommAlgebra→CommRing A) ˣ)
                        → Type (ℓ-suc ℓ)
 hasLocAlgUniversalProp A _ = (B : CommAlgebra R')
                            → (∀ s → s ∈ S' →  _⋆_ B s (1a B) ∈ (CommAlgebra→CommRing B) ˣ)
                            → isContr (CommAlgebraHom A B)

 S⋆1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → _⋆_ S⁻¹RAsCommAlg s (1a S⁻¹RAsCommAlg) ∈ S⁻¹Rˣ
 S⋆1⊆S⁻¹Rˣ s s∈S' = subst (_∈ S⁻¹Rˣ)
                    (cong [_] (≡-× (sym (·rRid s)) (Σ≡Prop (λ x → S' x .snd) (sym (·rRid _)))))
                    (S/1⊆S⁻¹Rˣ s s∈S')

 S⁻¹RHasAlgUniversalProp : hasLocAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ
 S⁻¹RHasAlgUniversalProp B' S⋆1⊆Bˣ = χᴬ , χᴬuniqueness
  where
  B = fromCommAlg B' .fst
  open CommRingStr (snd B) renaming (_·_ to _·b_ ; 1r to 1b ; ·Lid to ·bLid)

  φ : CommRingHom R' B
  φ = fromCommAlg B' .snd

  φS⊆Bˣ :  ∀ s → s ∈ S' → RingHom.f φ s ∈ B ˣ
  φS⊆Bˣ  = S⋆1⊆Bˣ

  χ : CommRingHom S⁻¹RAsCommRing B
  χ = S⁻¹RHasUniversalProp B φ φS⊆Bˣ .fst .fst

  χcomp : ∀ r → RingHom.f χ (r /1) ≡ RingHom.f φ r
  χcomp = funExt⁻ (S⁻¹RHasUniversalProp B φ φS⊆Bˣ .fst .snd)

  χᴬ : CommAlgebraHom S⁻¹RAsCommAlg B'
  f χᴬ = RingHom.f χ
  isHom+ χᴬ = RingHom.isHom+ χ
  isHom· χᴬ = RingHom.isHom· χ
  pres1 χᴬ = RingHom.pres1 χ
  comm⋆ χᴬ r x = path
   where
   path : RingHom.f χ ((r /1) ·ₗ x) ≡ _⋆_  B' r (RingHom.f χ x)
   path = RingHom.f χ ((r /1) ·ₗ x)           ≡⟨ RingHom.isHom· χ _ _ ⟩
          RingHom.f χ (r /1) ·b RingHom.f χ x ≡⟨ cong (_·b RingHom.f χ x) (χcomp r) ⟩
          RingHom.f φ r ·b RingHom.f χ x      ≡⟨ refl ⟩
          _⋆_  B' r 1b ·b RingHom.f χ x       ≡⟨ ⋆-lassoc B' _ _ _ ⟩
          _⋆_  B' r (1b ·b RingHom.f χ x)     ≡⟨ cong (_⋆_ B' r) (·bLid _) ⟩
          _⋆_  B' r (RingHom.f χ x) ∎


  χᴬuniqueness : (ψ : CommAlgebraHom S⁻¹RAsCommAlg B') → χᴬ ≡ ψ
  χᴬuniqueness ψ = AlgebraHomPath _ _ (cong RingHom.f (cong fst (χuniqueness (ψ' , funExt ψ'r/1≡φr))))
   where
   χuniqueness = S⁻¹RHasUniversalProp B φ φS⊆Bˣ .snd

   ψ' : CommRingHom S⁻¹RAsCommRing B
   RingHom.f ψ' = f ψ
   RingHom.pres1 ψ' = pres1 ψ
   RingHom.isHom+ ψ' x y = isHom+ ψ x y
   RingHom.isHom· ψ' x y = isHom· ψ x y

   ψ'r/1≡φr : ∀ r → f ψ (r /1) ≡ RingHom.f φ r
   ψ'r/1≡φr r = f ψ (r /1)                                   ≡⟨ cong (f ψ) (sym (·ₗ-rid _)) ⟩
                f ψ (_⋆_ S⁻¹RAsCommAlg r (1a S⁻¹RAsCommAlg)) ≡⟨ comm⋆ ψ _ _ ⟩
                _⋆_  B' r (f ψ (1a S⁻¹RAsCommAlg))           ≡⟨ cong (_⋆_  B' r) (pres1 ψ) ⟩
                _⋆_  B' r 1b ∎


 -- an immediate corrollary:
 isContrHomS⁻¹RS⁻¹R : isContr (CommAlgebraHom S⁻¹RAsCommAlg S⁻¹RAsCommAlg)
 isContrHomS⁻¹RS⁻¹R = S⁻¹RHasAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ


module AlgLocTwoSubsets (R' : CommRing {ℓ})
                        (S₁ : ℙ (fst R')) (S₁MultClosedSubset : isMultClosedSubset R' S₁)
                        (S₂ : ℙ (fst R')) (S₂MultClosedSubset : isMultClosedSubset R' S₂) where
 open isMultClosedSubset
 open CommRingStr (snd R') hiding (is-set)
 open Theory (CommRing→Ring R')
 open RingHom
 open Loc R' S₁ S₁MultClosedSubset renaming (S⁻¹R to S₁⁻¹R ;
                                             S⁻¹RAsCommRing to S₁⁻¹RAsCommRing)
 open Loc R' S₂ S₂MultClosedSubset renaming (S⁻¹R to S₂⁻¹R ;
                                             S⁻¹RAsCommRing to S₂⁻¹RAsCommRing)
 open AlgLoc R' S₁ S₁MultClosedSubset renaming (S⁻¹RAsCommAlg to S₁⁻¹RAsCommAlg)
 open AlgLoc R' S₂ S₂MultClosedSubset renaming (S⁻¹RAsCommAlg to S₂⁻¹RAsCommAlg)

 open CommAlgebra ⦃...⦄

 private
  R = fst R'
  S₁⁻¹Rˣ = S₁⁻¹RAsCommRing ˣ
  S₂⁻¹Rˣ = S₂⁻¹RAsCommRing ˣ
  instance
   _ = S₁⁻¹RAsCommAlg
   _ = S₂⁻¹RAsCommAlg


 isContrS₁⁻¹R≡S₂⁻¹R : (∀ s₁ → s₁ ∈ S₁ → s₁ ⋆ 1a ∈ S₂⁻¹Rˣ)
                    → (∀ s₂ → s₂ ∈ S₂ → s₂ ⋆ 1a ∈ S₁⁻¹Rˣ)
                    → isContr (S₁⁻¹RAsCommAlg ≡ S₂⁻¹RAsCommAlg)
 isContrS₁⁻¹R≡S₂⁻¹R S₁⊆S₂⁻¹Rˣ S₂⊆S₁⁻¹Rˣ = isOfHLevelRetractFromIso 0
                                          (equivToIso (invEquiv (CommAlgebraPath _ _ _)))
                                          isContrS₁⁻¹R≅S₂⁻¹R
  where
  isContrS₁⁻¹R≅S₂⁻¹R : isContr (CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg)
  isContrS₁⁻¹R≅S₂⁻¹R = {!!}
