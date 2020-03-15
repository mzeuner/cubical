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

infixr 5 ⟨_,_⟩∷_

data AssocList (A : Type₀) : Type₀ where
 ⟨⟩ : AssocList A
 ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
 per : ∀ a b xs →   ⟨ a , 1 ⟩∷ ⟨ b , 1 ⟩∷ xs
                  ≡ ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ xs
 agg : ∀ a m n xs →  ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs
                   ≡ ⟨ a , m + n ⟩∷ xs
 del : ∀ a xs → ⟨ a , 0 ⟩∷ xs ≡ xs
 trunc : isSet (AssocList A)

pattern ⟨_⟩ a = ⟨ a , 1 ⟩∷ ⟨⟩

multiPer : (a b : A) (m n : ℕ) (xs : AssocList A)
          → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
multiPer a b zero n xs = del a (⟨ b , n ⟩∷ xs) ∙ cong (λ ys → ⟨ b , n ⟩∷ ys) (sym (del a xs))
multiPer a b (suc m) zero xs = cong (λ ys → ⟨ a , suc m ⟩∷ ys) (del b xs) ∙ sym (del b (⟨ a , suc m ⟩∷ xs))
multiPer a b (suc m) (suc n) xs =  sym (agg a 1 m (⟨ b , suc n ⟩∷ xs))
                                 ∙ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (multiPer a b m (suc n) xs)
                                 ∙ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (sym (agg b 1 n (⟨ a , m ⟩∷ xs)))
                                 ∙ per a b (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs)
                                 ∙ cong (λ ys → ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ys) (multiPer b a n m xs)
                                 ∙ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (agg a 1 m (⟨ b , n ⟩∷ xs))
                                 ∙ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (multiPer a b (suc m) n xs)
                                 ∙ agg b 1 n (⟨ a , suc m ⟩∷ xs)




-- Show (AssocList A) ≃ (FMSet A)
φ : AssocList A → FMSet A
φ ⟨⟩ = []
φ (⟨ a , zero ⟩∷ xs) = φ xs
φ (⟨ a , suc n ⟩∷ xs) = a ∷ φ (⟨ a , n ⟩∷ xs)
φ (per a b xs i) = comm a b (φ xs) i
φ (agg a zero zero xs i) = φ xs
φ (agg a zero (suc n) xs i) = cong (λ ys → a ∷ φ ys) (agg a zero n xs) i
φ (agg a (suc m) n xs i) = cong (λ ys → a ∷ φ ys) (agg a m n xs) i
φ (del a xs i) = φ xs
φ (trunc xs ys p q i j) =  trunc (φ xs) (φ ys) (cong φ p) (cong φ q) i j



ψ : FMSet A → AssocList A
ψ [] = ⟨⟩
ψ (x ∷ xs) = ⟨ x , 1 ⟩∷ (ψ xs)
ψ (comm x y xs i) = per x y (ψ xs) i
ψ (trunc xs ys p q i j) = trunc (ψ xs) (ψ ys) (cong ψ p) (cong ψ q) i j
