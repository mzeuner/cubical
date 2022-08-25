{-

  This file contains a proof of the following fact:
  For a commutative ring R with elements f₁ , ... , fₙ ∈ R such that
  ⟨ f₁ , ... , fₙ ⟩ = ⟨ 1 ⟩ = R we get an (exact) equalizer diagram of the following form:

      0 → R → ∏ᵢ R[1/fᵢ] ⇉ ∏ᵢⱼ R[1/fᵢfⱼ]

  where the two maps ∏ᵢ R[1/fᵢ] → ∏ᵢⱼ R[1/fᵢfⱼ] are induced by the two canonical maps
  R[1/fᵢ] → R[1/fᵢfⱼ] and R[1/fⱼ] → R[1/fᵢfⱼ].

  But expressed as limits, that's what we need for structure sheaf
  in the case n=2 this will give us what is in Localisation.Pullback

-}




{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈ₚ_)
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order hiding (_<_)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order renaming (_<'Fin_ to _<_)

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice.Instances.NatMax

open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.DistLatticeSheaf.Diagram

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level


-- TODO: deal with case zero later
module _ (R' : CommRing ℓ) {n : ℕ} (f : FinVec (fst R') (suc n)) where
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommIdeal R' hiding (subst-∈)
 open InvertingElementsBase R'
 open Exponentiation R'
 open CommRingStr ⦃...⦄

 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]
  ⟨f₀,⋯,fₙ⟩ = ⟨ f ⟩[ R' ]

  instance
   _ = R' .snd

  module L i = Loc R' [ f i ⁿ|n≥0] (powersFormMultClosedSubset (f i))
  module U i = S⁻¹RUniversalProp R' [ f i ⁿ|n≥0] (powersFormMultClosedSubset (f i))
  module LP i j = Loc R' [ f i · f j ⁿ|n≥0] (powersFormMultClosedSubset (f i · f j))
  module UP i j = S⁻¹RUniversalProp R' [ f i · f j ⁿ|n≥0] (powersFormMultClosedSubset (f i · f j))

  -- a lot of syntax to make things readable
  0at : (i : Fin (suc n)) →  R[1/ (f i) ]
  0at i = R[1/ (f i) ]AsCommRing .snd .CommRingStr.0r

  _/1ˢ : R → {i : Fin (suc n)} →  R[1/ (f i) ]
  (r /1ˢ) {i = i} = U._/1 i r

  _/1ᵖ : R → {i j : Fin (suc n)} →  R[1/ (f i) · (f j) ]
  (r /1ᵖ) {i = i} {j = j} = UP._/1 i j r

 -- to be upstreamed
 recFin : {m : ℕ} {P : Fin m → Type ℓ'}
          {B : Type ℓ''} (isPropB : isProp B)
        → ((∀ i → P i) → B)
       ---------------------
        → ((∀ i → ∥ P i ∥₁) → B)
 recFin {m = zero} _ untruncHyp _ = untruncHyp (λ ())
 recFin {m = suc m} {P = P} {B = B} isPropB untruncHyp truncFam =
   CurriedishTrunc (truncFam zero) (truncFam ∘ suc)
   where
   Curriedish : P zero → (∀ i → ∥ P (suc i) ∥₁) → B
   Curriedish p₀ truncFamSuc = recFin isPropB
                              (λ famSuc → untruncHyp (λ { zero → p₀ ; (suc i) → famSuc i }))
                                truncFamSuc

   CurriedishTrunc : ∥ P zero ∥₁ → (∀ i → ∥ P (suc i) ∥₁) → B
   CurriedishTrunc = PT.rec (isProp→ isPropB) Curriedish


 -- This lemma proves that if ⟨ f₀ ,..., fₙ ⟩ ≡ R,
 -- then we get an exact sequence
 --   0 → R → ∏ᵢ R[1/fᵢ]
 -- sending r : R to r/1 in R[1/fᵢ] for each i
 injectivityLemma : 1r ∈ ⟨f₀,⋯,fₙ⟩ → ∀ (x : R) → (∀ i → x /1ˢ ≡ 0at i) → x ≡ 0r
 injectivityLemma 1∈⟨f₀,⋯,fₙ⟩ x x/1≡0 = recFin (is-set _ _) annihilatorHelper exAnnihilator
  where
  exAnnihilator : ∀ i → ∃[ s ∈ L.S i ] (fst s · x · 1r ≡ fst s · 0r · 1r)
  exAnnihilator i = isEquivRel→TruncIso (L.locIsEquivRel i) _ _ .fun (x/1≡0 i)

  annihilatorHelper : (∀ i → Σ[ s ∈ L.S i ] (fst s · x · 1r ≡ fst s · 0r · 1r))
                    → x ≡ 0r
  annihilatorHelper ann = recFin (is-set _ _) exponentHelper uIsPower
    where
    u : FinVec R (suc n)
    u i = ann i .fst .fst

    uIsPower : ∀ i → u i ∈ₚ [ (f i) ⁿ|n≥0]
    uIsPower i = ann i .fst .snd

    ux≡0 : ∀ i → u i · x ≡ 0r
    ux≡0 i = sym (·IdR _) ∙ ann i .snd ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·IdR _)

    exponentHelper : (∀ i → Σ[ m ∈ ℕ ] u i ≡ f i ^ m)
                   → x ≡ 0r
    exponentHelper pows = PT.rec (is-set _ _) Σhelper (GeneratingPowers.thm R' l _ _ 1∈⟨f₀,⋯,fₙ⟩)
      where
      m : FinVec ℕ (suc n)
      m i = pows i .fst

      u≡fᵐ : ∀ i → u i ≡ f i ^ m i
      u≡fᵐ i = pows i .snd

      l = Max m

      fˡ : FinVec R (suc n)
      fˡ i = f i ^ l

      fˡx≡0 : ∀ i → f i ^ l · x ≡ 0r
      fˡx≡0 i =
        f i ^ l · x                     ≡⟨ cong (λ k → f i ^ k · x)
                                             (sym (≤-∸-+-cancel (ind≤Max m i))) ⟩
        f i ^ ((l ∸ m i) +ℕ m i) · x    ≡⟨ cong (_· x) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩
        f i ^ (l ∸ m i) · f i ^ m i · x ≡⟨ cong (λ y → f i ^ (l ∸ m i) · y · x)
                                                (sym (u≡fᵐ i)) ⟩
        f i ^ (l ∸ m i) · u i · x       ≡⟨ sym (·Assoc _ _ _) ⟩
        f i ^ (l ∸ m i) · (u i · x)     ≡⟨ cong (f i ^ (l ∸ m i) ·_) (ux≡0 i) ⟩
        f i ^ (l ∸ m i) · 0r            ≡⟨ 0RightAnnihilates _ ⟩
        0r ∎


      Σhelper : Σ[ α ∈ FinVec R (suc n) ] 1r ≡ ∑ (λ i → α i · f i ^ l)
              → x ≡ 0r
      Σhelper (α , 1≡∑αfˡ) =
        x                                   ≡⟨ sym (·IdL _) ⟩
        1r · x                              ≡⟨ cong (_· x) 1≡∑αfˡ ⟩
        ∑ (λ i → α i · f i ^ l) · x         ≡⟨ ∑Mulldist _ _ ⟩
        ∑ (λ i → α i · f i ^ l · x)         ≡⟨ ∑Ext (λ i → sym (·Assoc (α i)
                                                                  (f i ^ l) x)) ⟩
        ∑ (λ i → α i · (f i ^ l · x))       ≡⟨ ∑Ext (λ i → cong (α i ·_) (fˡx≡0 i)) ⟩
        ∑ (λ i → α i · 0r)                  ≡⟨ ∑Ext (λ i → 0RightAnnihilates (α i)) ⟩
        ∑ (replicateFinVec (suc n) 0r)      ≡⟨ ∑0r (suc n) ⟩
        0r ∎


 -- the morphisms into localisations at products from the left/right
 -- we need to define them by hand as using RadicalLemma wouldn't compute later
 χˡ : (i j : Fin (suc n)) → CommRingHom R[1/ f i ]AsCommRing
                                        R[1/ f i · f j ]AsCommRing
 χˡ i j = U.S⁻¹RHasUniversalProp i _ (UP./1AsCommRingHom i j) unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ (f i) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f j ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     useSolver1 : ∀ a b → 1r · (a · b) · 1r ≡ a · b
     useSolver1 = solve R'
     useSolver2 : ∀ a → a ≡ (1r · 1r) · (1r · a)
     useSolver2 = solve R'

     path : (n : ℕ) → 1r · (f i ^ n · f j ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = useSolver1 _ _ ∙ sym (^-ldist-· (f i) (f j) n) ∙ useSolver2 _


 χʳ : (i j : Fin (suc n)) → CommRingHom R[1/ f j ]AsCommRing
                                        R[1/ f i · f j ]AsCommRing
 χʳ i j = U.S⁻¹RHasUniversalProp j _ (UP./1AsCommRingHom i j) unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ (f j) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f i ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     useSolver1 : ∀ a b → 1r · (a · b) · 1r ≡ b · a
     useSolver1 = solve R'
     useSolver2 : ∀ a → a ≡ (1r · 1r) · (1r · a)
     useSolver2 = solve R'

     path : (n : ℕ) → 1r · (f j ^ n · f i ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = useSolver1 _ _ ∙ sym (^-ldist-· (f i) (f j) n) ∙ useSolver2 _


 -- to be upstreamed / what should it be called
 recFin< : {m : ℕ} {P : {i j : Fin m} → i < j → Type ℓ'}
            {B : Type ℓ''} (isPropB : isProp B)
          → ((∀ {i} {j} (i<j : i < j) → P i<j) → B)
         ---------------------------------------------------
          → ((∀ {i} {j} (i<j : i < j) → ∥ P i<j ∥₁) → B)
 recFin< {m = zero} isPropB untruncHyp truncs = untruncHyp (λ {i} → ⊥.rec (¬Fin0 i))
 recFin< {m = suc m} {P = P} {B = B} isPropB untruncHyp truncs =
   curriedishTrunc {!!}
                     λ i<j → truncs (s≤s i<j)
   where
   curriedish : (∀ j (0<j : zero < j) → P 0<j)
              → (∀ {i j : Fin m} (i<j : i < j) → ∥ P (s≤s i<j) ∥₁)
              → B
   curriedish p₀ truncFamSuc = recFin< isPropB
     (λ famSuc → untruncHyp (λ { {i = zero} 0<j → p₀ _ 0<j
                               ; {i = suc i} {j = zero} ()
                               ; {i = suc i} {j = suc j} (s≤s i<j) → famSuc i<j}))
          truncFamSuc

   curriedishTrunc : (∀ j → ∥ ((0<j : zero < j) → P 0<j) ∥₁)
                   → (∀ {i j : Fin m} (i<j : i < j) → ∥ P (s≤s i<j) ∥₁)
                   → B
   curriedishTrunc = recFin (isProp→ isPropB) curriedish

 -- this will do all the heavy lifting
 equalizerLemma : 1r ∈ ⟨f₀,⋯,fₙ⟩
                → ∀ (x : (i : Fin (suc n)) → R[1/ f i ]) -- s.t.
                → (∀ {i} {j} → i < j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
                → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ x i)
 equalizerLemma 1∈⟨f₀,⋯,fₙ⟩ = invElPropElimN n f _
                                              (λ _ → isPropΠ (λ _ → isProp∃!))
                                                baseCase
   where
   baseCase : ∀ (r : FinVec R (suc n)) (m : ℕ)
            → (∀ {i} {j} → i < j
                 → χˡ i j .fst ([ r i , f i ^ m , ∣ m , refl ∣₁ ])
                 ≡ χʳ i j .fst ([ r j , f j ^ m , ∣ m , refl ∣₁ ]))
            → ∃![ y ∈ R ] ∀ i → (y /1ˢ) ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ]
   baseCase r m pairHyp = recFin< isProp∃! annihilatorHelper exAnnihilator
     where
     -- This computes because we defined the χ by hand
     exAnnihilator : ∀ {i} {j} → i < j
                   → ∃[ s ∈ LP.S i j ] -- s.t.
                       fst s · (r i · transport refl (f j ^ m))
                             · (1r · transport refl ((f i · f j) ^ m))
                     ≡ fst s · (r j · transport refl (f i ^ m))
                             · (1r · transport refl ((f i · f j) ^ m))
     exAnnihilator i<j = isEquivRel→TruncIso (LP.locIsEquivRel _ _) _ _ .fun
                                             (pairHyp i<j)
     -- sᵢⱼ = fᵢfⱼ ^ lᵢⱼ, so need to take max over all of these...
     annihilatorHelper : (∀ {i} {j} → i < j
                           → Σ[ s ∈ LP.S i j ] -- s.t.
                               fst s · (r i · transport refl (f j ^ m))
                                     · (1r · transport refl ((f i · f j) ^ m))
                             ≡ fst s · (r j · transport refl (f i ^ m))
                                     · (1r · transport refl ((f i · f j) ^ m)))
                       → ∃![ y ∈ R ] ∀ i → (y /1ˢ) ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ]
     annihilatorHelper anns = recFin< isProp∃! exponentHelper sIsPow
       where
       -- notation
       s : {i j : Fin (suc n)} → i < j → R
       s i<j = anns i<j .fst .fst

       sIsPow : ∀ {i} {j} (i<j : i < j) → s i<j ∈ₚ [ (f i · f j) ⁿ|n≥0]
       sIsPow i<j = anns i<j .fst .snd

       sIsAnn : ∀ {i} {j} (i<j : i < j)
              → s i<j · r i · f j ^ m · (f i · f j) ^ m
              ≡ s i<j · r j · f i ^ m · (f i · f j) ^ m
       sIsAnn {i = i} {j = j} i<j =
           s i<j · r i · f j ^ m · (f i · f j) ^ m
         ≡⟨ transpHelper _ _ _ _ ⟩
           s i<j · r i · transport refl (f j ^ m) · transport refl ((f i · f j) ^ m)
         ≡⟨ useSolver _ _ _ _ ⟩
           s i<j · (r i · transport refl (f j ^ m))
                 · (1r · transport refl ((f i · f j) ^ m))
         ≡⟨ anns i<j .snd ⟩
           s i<j · (r j · transport refl (f i ^ m))
                 · (1r · transport refl ((f i · f j) ^ m))
         ≡⟨ sym (useSolver _ _ _ _) ⟩
           s i<j · r j · transport refl (f i ^ m) · transport refl ((f i · f j) ^ m)
         ≡⟨ sym (transpHelper _ _ _ _) ⟩
           s i<j · r j · f i ^ m · (f i · f j) ^ m ∎
         where
         transpHelper : ∀ a b c d → a · b · c · d
                                  ≡ a · b · transport refl c · transport refl d
         transpHelper a b c d i = a · b · transportRefl c (~ i) · transportRefl d (~ i)
         useSolver : ∀ a b c d → a · b · c · d ≡ a · (b · c) · (1r · d)
         useSolver = solve R'

       exponentHelper : (∀ {i} {j} (i<j : i < j)
                           → Σ[ l ∈ ℕ ] s i<j ≡ (f i · f j) ^ l)
                      → ∃![ y ∈ R ] ∀ i → (y /1ˢ) ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ]
       exponentHelper = {!!}
