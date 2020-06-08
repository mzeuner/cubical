{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.ZigZag.Applications.FFMS where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
-- open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Empty as ⊥
open import Cubical.Structures.MultiSet
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
-- open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
-- open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.ZigZag.Base as ZigZag



private
 variable
  ℓ : Level
  A : Type ℓ



-- Yet another way of defining finite multisets:
supp : {A : Type ℓ} → (A → ℕ) → Type ℓ
supp {A = A} f = Σ[ a ∈ A ] (0 < f a)

fin-supp : {A : Type ℓ} → (A → ℕ) → Type ℓ
fin-supp f = Σ[ n ∈ ℕ ] (Fin n ≃ supp f)

FFMS : (A : Type ℓ) → Type ℓ
FFMS A = Σ[ f ∈ (A → ℕ) ] ∥ fin-supp f ∥

FFMScount : A → FFMS A → ℕ
FFMScount a f = f .fst a


--_∪_ : FFMS A → FFMS A → FFMS A
-- (f , α) ∪ (g , β) = (λ a → (f a) + (g a)) , {!!}


-- We need some results about finite support first
Supp : (f : A → ℕ) → ℙ {ℓ = ℓ-zero} A
Supp f a = (0 < f a) , m≤n-isProp


lemma₁ : ∀ (f g : A → ℕ) → (∀ a → f a ≤ g a) → Supp f ⊆ Supp g
lemma₁ f g pw≤ a ineq = ≤-trans ineq (pw≤ a)

Thm₁ : ∀ {A : Type ℓ} (n : ℕ) (X Y : ℙ A) → (∀ a → Dec (a ∈ X)) → X ⊆ Y
     → Fin n ≃ Σ A (_∈ Y) → Σ[ m ∈ ℕ ] Fin m ≃ Σ A (_∈ X)
Thm₁ {A = A} zero X Y dec_∈X X⊆Y e = zero , isoToEquiv
                                   (iso (λ ()) (λ (a , a∈X) → invEquiv e .fst (a , X⊆Y a a∈X))
                                   (λ (a , a∈X) → ⊥.rec (¬Fin0 (invEquiv e .fst (a , X⊆Y a a∈X)))) λ ())
Thm₁ {A = A} (suc n) X Y dec_∈X X⊆Y e with dec_∈X (e .fst zero .fst)
...                           | yes p = suc m , {!!}
 where
 a₀ = (e .fst zero .fst)

 X' : ℙ A
 X' a = X a ⊓ (a ≢ₚ a₀)

 Y' : ℙ A
 Y' a = Y a ⊓ (a ≢ₚ a₀)

 X'⊆Y' : X' ⊆ Y'
 X'⊆Y' a a∈X' = X⊆Y a (a∈X' .fst) , a∈X' .snd

 dec_∈X' : ∀ a → Dec (a ∈ X')
 dec_∈X' a = {!!} --do we need that A is discrete?

 e' : Fin n ≃ Σ A (_∈ Y')
 e' = {!!}

 m = Thm₁ {A = A} n  X' Y' dec_∈X' X'⊆Y' e' .fst
 f : Fin m ≃ Σ A (_∈ X')
 f = Thm₁ {A = A} n  X' Y' dec_∈X' X'⊆Y' e' .snd

...                           | no ¬p = {!!}
