{-# OPTIONS --safe #-}

module Cubical.Foundations.ProjectiveLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

private
 variable
  ℓ ℓ' ℓ'' ℓ''' : Level

record isPoset (J : Type ℓ) (_≤_ : J → J → Type ℓ') : Type (ℓ-max ℓ ℓ') where
 field
  reflexivity : ∀ j → j ≤ j
  transitivity : ∀ {j k l} → j ≤ k → k ≤ l → j ≤ l
  -- isset : isSet J
  -- propvalued : ∀ j k → isProp (j ≤ k)

record isProjectiveSystem (J : Type ℓ) (_≤_ : J → J → Type ℓ') (isposet : isPoset J _≤_)
                          (X : J → Type ℓ'')
                          (μ : ∀ {i j} → i ≤ j → X j → X i) : Type (ℓ-max ℓ'' (ℓ-max ℓ ℓ')) where
 open isPoset ⦃...⦄
 instance
  _ = isposet
 field
  refl-id : ∀ (i : J) (x : X i) → μ (reflexivity i) x ≡ x
  compatability : ∀ {i j k : J} (i≤j : i ≤ j) (j≤k : j ≤ k) (x : X k)
                → μ i≤j (μ j≤k x) ≡ μ (transitivity i≤j j≤k) x


module _ (J : Type ℓ) (_≤_ : J → J → Type ℓ') (isposet : isPoset J _≤_)
         (X : J → Type ℓ'') (μ : ∀ {i j} → i ≤ j → X j → X i)
         (isprojsys : isProjectiveSystem J _≤_ isposet X μ) where
 open isPoset ⦃...⦄
 open isProjectiveSystem ⦃...⦄
 instance
  _ = isposet
  _ = isprojsys

 projLim : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
 projLim = Σ[ f ∈ ((j : J) → X j) ] (∀ {i j} (i≤j : i ≤ j) → f i ≡ μ i≤j (f j))

 π : (j : J) → projLim → X j
 π j x = x .fst j

 π-compatability : ∀ {i j} (i≤j : i ≤ j) (x : projLim) → π i x ≡ μ i≤j (π j x)
 π-compatability i≤j x = x .snd i≤j

 inducedMap : (Z : Type ℓ''') (h : (j : J) → Z → X j)
            → (∀ {i j} (i≤j : i ≤ j) (z : Z) → h i z ≡ μ i≤j (h j z))
            → Σ[ h∞ ∈ (Z → projLim) ] (∀ i z → h i z ≡ π i (h∞ z))
 inducedMap Z h hCompat = (λ z → (λ j → h j z) , λ i≤j → hCompat i≤j z) , λ _ _ → refl

 inducedMapUniq : (∀ j → isSet (X j))
                → (Z : Type ℓ''') → (h : (j : J) → Z → X j)
                → (∀ {i j} (i≤j : i ≤ j) (z : Z) → h i z ≡ μ i≤j (h j z))
                → isProp (Σ[ h∞ ∈ (Z → projLim) ] (∀ i z → h i z ≡ π i (h∞ z)))
 inducedMapUniq Xset Z h hCompat (h∞ , h∞Compat) (g∞ , g∞Compat) =
                Σ≡Prop (λ _ → isPropΠ2 λ _ _ → Xset _ _ _)
                (funExt (λ z → Σ≡Prop (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → Xset _ _ _)))
                 (funExt λ j → sym (h∞Compat j z) ∙ g∞Compat j z)))
