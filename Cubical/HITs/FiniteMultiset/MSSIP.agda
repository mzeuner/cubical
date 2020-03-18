{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.MSSIP where

open import Cubical.Foundations.Everything
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.HITs.FiniteMultiset.Properties

open import Cubical.Data.Nat   using (ℕ; zero; suc; _+_; +-zero; +-comm)

private
  variable
    ℓ : Level
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
 trun : isSet (AssocList A)

pattern ⟨_⟩ a = ⟨ a , 1 ⟩∷ ⟨⟩

multiPer : (a b : A) (m n : ℕ) (xs : AssocList A)
          → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
multiPer a b zero n xs = del a (⟨ b , n ⟩∷ xs) ∙ cong (λ ys → ⟨ b , n ⟩∷ ys) (sym (del a xs))
multiPer a b (suc m) zero xs = cong (λ ys → ⟨ a , suc m ⟩∷ ys) (del b xs) ∙ sym (del b (⟨ a , suc m ⟩∷ xs))
multiPer a b (suc m) (suc n) xs =

 ⟨ a , suc m ⟩∷ ⟨ b , suc n ⟩∷ xs               ≡⟨ sym (agg a 1 m (⟨ b , suc n ⟩∷ xs)) ⟩
 ⟨ a , 1 ⟩∷ ⟨ a , m ⟩∷ ⟨ b , suc n ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (multiPer a b m (suc n) xs) ⟩
 ⟨ a , 1 ⟩∷ ⟨ b , suc n ⟩∷ ⟨ a , m ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ a , 1 ⟩∷ ys) (sym (agg b 1 n (⟨ a , m ⟩∷ xs))) ⟩
 ⟨ a , 1 ⟩∷ ⟨ b , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs ≡⟨ per a b (⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ys) (multiPer b a n m xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (agg a 1 m (⟨ b , n ⟩∷ xs)) ⟩
 ⟨ b , 1 ⟩∷ ⟨ a , suc m ⟩∷ ⟨ b , n ⟩∷ xs        ≡⟨ cong (λ ys → ⟨ b , 1 ⟩∷ ys) (multiPer a b (suc m) n xs) ⟩
 ⟨ b , 1 ⟩∷ ⟨ b , n ⟩∷ ⟨ a , suc m ⟩∷ xs        ≡⟨ agg b 1 n (⟨ a , suc m ⟩∷ xs) ⟩
 ⟨ b , suc n ⟩∷ ⟨ a , suc m ⟩∷ xs               ∎



--Recursion principle for association lists
module ALelim {ℓ} {B : AssocList A → Type ℓ}
       (⟨⟩* : B ⟨⟩) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) {xs : AssocList A} → B xs → B (⟨ x , n ⟩∷ xs))
       (per* :  (x y : A) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (per x y xs i)) (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b) (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b))
       (agg* :  (x : A) (m n : ℕ) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (agg x m n xs i)) (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b) (⟨ x , m + n ⟩∷* b))
       (del* :  (x : A) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (del x xs i)) (⟨ x , 0 ⟩∷* b) b)
       (trunc* : (xs : AssocList A) → isSet (B xs)) where

 f : (xs : AssocList A) → B xs
 f ⟨⟩ = ⟨⟩*
 f (⟨ a , n ⟩∷ xs) = ⟨ a , n ⟩∷* f xs
 f (per a b xs i) = per* a b (f xs) i
 f (agg a m n xs i) = agg* a m n (f xs) i
 f (del a xs i) = del* a (f xs) i
 f (trun xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys) (cong f p) (cong f q) (trun xs ys p q) i j



module ALelimProp {ℓ} {B : AssocList A → Type ℓ} (BProp : {xs : AssocList A} → isProp (B xs))
       (⟨⟩* : B ⟨⟩) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) {xs : AssocList A} → B xs → B (⟨ x , n ⟩∷ xs)) where

 f : (xs : AssocList A) → B xs
 f = ALelim.f ⟨⟩* ⟨_,_⟩∷*_
      (λ x y {xs} b → toPathP (BProp (transp (λ i → B (per x y xs i)) i0 (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b)) (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b)))
      (λ x m n {xs} b → toPathP (BProp (transp (λ i → B (agg x m n xs i)) i0 (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b)) (⟨ x , m + n ⟩∷* b)))
      (λ x {xs} b → toPathP (BProp (transp (λ i → B (del x xs i)) i0 (⟨ x , 0 ⟩∷* b)) b))
      (λ xs → isProp→isSet BProp)



module ALrec {ℓ} {B : Type ℓ} (BType : isSet B)
       (⟨⟩* : B) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) → B → B)
       (per* :  (x y : A) (b : B) → (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b) ≡ (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b))
       (agg* :  (x : A) (m n : ℕ) (b : B) → (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b) ≡ (⟨ x , m + n ⟩∷* b))
       (del* :  (x : A) (b : B) → (⟨ x , 0 ⟩∷* b) ≡ b) where

 f : AssocList A → B
 f = ALelim.f ⟨⟩* (λ x n b → ⟨ x , n ⟩∷* b) (λ x y b → per* x y b) (λ x m n b → agg* x m n b) (λ x b → del* x b) (λ _ → BType)





-- Show (AssocList A) ≃ (FMSet A)
multi-∷ : A → ℕ → FMSet A → FMSet A
multi-∷ x zero xs = xs
multi-∷ x (suc n) xs = x ∷ multi-∷ x n xs

multi-∷-agg : (x : A) (m n : ℕ) (b : FMSet A) → multi-∷ x m (multi-∷ x n b) ≡ multi-∷ x (m + n) b
multi-∷-agg x zero n b = refl
multi-∷-agg x (suc m) n b i = x ∷ (multi-∷-agg x m n b i)

φ : AssocList A → FMSet A
φ = ALrec.f trunc [] multi-∷ comm multi-∷-agg λ _ _ → refl
-- φ ⟨⟩ = []
-- φ (⟨ a , zero ⟩∷ xs) = φ xs
-- φ (⟨ a , suc n ⟩∷ xs) = a ∷ φ (⟨ a , n ⟩∷ xs)
-- φ (per a b xs i) = comm a b (φ xs) i
-- φ (agg a zero zero xs i) = φ xs
-- φ (agg a zero (suc n) xs i) = cong (λ ys → a ∷ φ ys) (agg a zero n xs) i
-- φ (agg a (suc m) n xs i) = cong (λ ys → a ∷ φ ys) (agg a m n xs) i
-- φ (del a xs i) = φ xs
-- φ (trun xs ys p q i j) = trunc (φ xs) (φ ys) (cong φ p) (cong φ q) i j




ψ : FMSet A → AssocList A
ψ = Rec.f trun ⟨⟩ (λ x xs → ⟨ x , 1 ⟩∷ xs) per
-- ψ [] = ⟨⟩
-- ψ (x ∷ xs) = ⟨ x , 1 ⟩∷ (ψ xs)
-- ψ (comm x y xs i) = per x y (ψ xs) i
-- ψ (trunc xs ys p q i j) = trun (ψ xs) (ψ ys) (cong ψ p) (cong ψ q) i j




η : section {A = AssocList A} φ ψ
η = ElimProp.f (trunc _ _) refl (λ x p → cong (λ ys → x ∷ ys) p)


-- need a little lemma for other direction
multi-∷-id : (x : A) (n : ℕ) (u : FMSet A)
            → ψ (multi-∷ x n u) ≡ ⟨ x , n ⟩∷ ψ u
multi-∷-id x zero u = sym (del x (ψ u))
multi-∷-id x (suc n) u = ψ (multi-∷ x (suc n) u)     ≡⟨ cong (λ ys → ⟨ x , 1 ⟩∷ ys) (multi-∷-id x n u) ⟩
                         ⟨ x , 1 ⟩∷ ⟨ x , n ⟩∷ (ψ u) ≡⟨ agg x 1 n (ψ u) ⟩
                         ⟨ x , (suc n) ⟩∷ (ψ u)      ∎

ε : retract {A = AssocList A} φ ψ
ε = ALelimProp.f (trun _ _) refl (λ x n {xs} p → (multi-∷-id x n (φ xs)) ∙ cong (λ ys → ⟨ x , n ⟩∷ ys) p)




AssocList≃FMSet : ∀ {A} → AssocList A ≃ FMSet A
AssocList≃FMSet = isoToEquiv (iso φ ψ η ε)
