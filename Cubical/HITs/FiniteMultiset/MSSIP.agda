{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.MSSIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.HITs.FiniteMultiset.Properties

open import Cubical.Data.Nat   using (ℕ; zero; suc; _+_; +-zero; +-comm)

private
  variable
    A : Type₀

infixr 5 _⟨_⟩∷_

data AssocList (A : Type₀) : Type₀ where
 ⟨⟩ : AssocList A
 ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
 per : ∀ a b m n xs →  ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs
                     ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
 agg : ∀ a m n xs →  ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs
                   ≡ ⟨ a , m + n ⟩∷ xs
 del : ∀ a xs → ⟨ a , 0 ⟩∷ xs ≡ xs
 trunc : isSet (AssocList A)
 
pattern ⟨_⟩ a = ⟨ a , 1 ⟩∷ ⟨⟩



φ : AssocList A → FMSet A
φ ⟨⟩ = []
φ (⟨ a , 0 ⟩∷ xs) = φ xs
φ (⟨ a , suc n ⟩∷ xs) = a ∷ φ (⟨ a , n ⟩∷ xs)
φ (per a b zero zero xs i) = φ xs
φ (per a b zero (suc n) xs i) = b ∷ φ (per a b zero n xs i)
φ (per a b (suc m) zero xs i) = a ∷ φ (per a b m zero xs i)
φ (per a b (suc m) (suc n) xs i) = p i 
 where 
 p₁ : a ∷ φ (⟨ a , m ⟩∷ ⟨ b , suc n ⟩∷ xs) ≡ a ∷ φ (⟨ b , suc n ⟩∷ ⟨ a , m ⟩∷ xs)
 p₁ = {!!}
 
 p₂ : a ∷ b ∷ φ (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs) ≡ b ∷ a ∷ φ (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs)
 p₂ = {!!}
 
 p₃ : b ∷ a ∷ φ (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs) ≡ b ∷ a ∷ φ (⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs)
 p₃ = {!!}
 
 p₄ : b ∷ a ∷ φ (⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs) ≡ b ∷ φ (⟨ b , n ⟩∷ ⟨ a , suc m ⟩∷ xs)
 p₄ = {!!}
 
 p :  a ∷ φ (⟨ a , m ⟩∷ ⟨ b , suc n ⟩∷ xs) ≡ b ∷ φ (⟨ b , n ⟩∷ ⟨ a , suc m ⟩∷ xs)
 p = {!!} --(p₁ ∙ p₂ ∙ p₃ ∙ p₄)
 
φ (agg a m n xs i) = {!!}
φ (del a xs i) = φ xs
φ (trunc xs ys p q i j) = trunc (φ xs) (φ ys) (cong φ p) (cong φ q) i j



ψ : FMSet A → AssocList A
ψ [] = ⟨⟩
ψ (x ∷ xs) = ⟨ x , 1 ⟩∷ (ψ xs)
ψ (comm x y xs i) = per x y 1 1 (ψ xs) i
ψ (trunc xs ys p q i j) = trunc (ψ xs) (ψ ys) (cong ψ p) (cong ψ q) i j
