{-

This file introduces the "powerset" of a type in the style of
Escardó's lecture notes:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#propositionalextensionality

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

ℙ : Type ℓ → Type (ℓ-suc ℓ)
ℙ X = X → hProp _

isSetℙ : isSet (ℙ X)
isSetℙ = isSetΠ λ x → isSetHProp

infix 5 _∈_

_∈_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∈ A = ⟨ A x ⟩

_⊆_ : {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-isProp : (A : ℙ X) (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

⊆-isProp : (A B : ℙ X) → isProp (A ⊆ B)
⊆-isProp A B = isPropΠ2 (λ x _ → ∈-isProp B x)

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl A x = idfun (x ∈ A)

⊆-trans : {A B C : ℙ X} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A⊆B B⊆C _ x∈A = B⊆C _ (A⊆B _ x∈A)

subst-∈ : (A : ℙ X) {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

-- an equivalent description of equality of subsets
-- that doesn't increase the universe level
_≡ᴾ_ : {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
A ≡ᴾ B = (A ⊆ B) × (B ⊆ A)

-- composition is just concatenation
_∙ᴾ_ : {A B C : ℙ X} → A ≡ᴾ B → B ≡ᴾ C → A ≡ᴾ C
fst (p ∙ᴾ q) = ⊆-trans (fst p) (fst q)
snd (p ∙ᴾ q) = ⊆-trans (snd q) (snd p)

⊆-refl-consequence : (A B : ℙ X) → A ≡ B → A ≡ᴾ B
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : ℙ X) → A ≡ᴾ B → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) (φ x) (ψ x)))

⊆-extensionalityEquiv : (A B : ℙ X) → A ≡ᴾ B ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSetℙ A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))

-- Is there are more direct proof?
congᴾ : {A B : ℙ X} (F : ℙ X → ℙ Y) → A ≡ᴾ B → F A ≡ᴾ F B
congᴾ F = equivFun (invEquiv (⊆-extensionalityEquiv _ _))
        ∘ cong F ∘ equivFun (⊆-extensionalityEquiv _ _)
