{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients.ZigZagRel where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Structures.MultiSet renaming (member-structure to S; member-iso to ι; Member-is-SNS to SNS[S,ι])
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.FiniteMultiset as FMS
open import Cubical.HITs.AssocList as AL renaming (AssocList to AList)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
 variable
  ℓ : Level
  

isZigZagComplete : {A B : Type ℓ} (R : A → B → Type ℓ) → Type ℓ
isZigZagComplete R = ∀ {a b a' b'} → R a b → R a' b → R a' b' → R a b'

isBisimulation : {A B : Type ℓ} (R : A → B → Type ℓ) (f : A → B) (g : B → A) → Type ℓ
isBisimulation R f g =  isZigZagComplete R
                      × (∀ a → R a (f a))
                      × (∀ b → R (g b) b)

module CarlosThm (A B : Type ℓ) (R : A → B → Type ℓ) (f : A → B) (g : B → A) (isBisRfg : isBisimulation R f g) where
 zigzag : isZigZagComplete R
 zigzag = isBisRfg .fst
 η' = isBisRfg .snd .fst
 ε' = isBisRfg .snd .snd

 Rᴬ : A → A → Type ℓ
 Rᴬ a a' = Σ[ b ∈ B ] (R a b × R a' b)
 
 Rᴮ : B → B → Type ℓ
 Rᴮ b b' = Σ[ a ∈ A ] (R a b × R a b')

 X = A / Rᴬ
 Y = B / Rᴮ

 φ : X → Y
 φ _/_.[ a ] = _/_.[ f a ]
 φ (eq/ a a' r i) = eq/ (f a) (f a') s i
   where
   s : Rᴮ (f a) (f a')
   s = a , η' a , zigzag (r .snd .fst) (r .snd .snd) (η' a')
 φ (squash/ x x₁ p q i j) = squash/ (φ x) (φ x₁) (cong φ p) (cong φ q) i j

 ψ : Y → X
 ψ _/_.[ b ] = _/_.[ g b ]
 ψ (eq/ b b' s i) = eq/ (g b) (g b') r i
  where
  r : Rᴬ (g b) (g b')
  r = b' , zigzag (ε' b) (s .snd .fst) (s .snd .snd) , ε' b'
 ψ (squash/ y y₁ p q i j) =  squash/ (ψ y) (ψ y₁) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η y = elimProp (λ y → squash/ (φ (ψ y)) y) (λ b → eq/ (f (g b)) b (g b , η' (g b) , ε' b)) y

 ε : retract φ ψ
 ε x = elimProp (λ x → squash/ (ψ (φ x)) x) (λ a → eq/ (g (f a)) a (f a , ε' (f a) , η' a)) x

 Thm3 : X ≃ Y
 Thm3 = isoToEquiv (iso φ ψ η ε)


-- Now for the applications: 
-- defining association lists without higher constructors
data AssocList (A : Type₀) : Type₀ where
 ⟨⟩ : AssocList A
 ⟨_,_⟩∷_ : A → ℕ → AssocList A → AssocList A

infixr 5 ⟨_,_⟩∷_

module _(A : Type₀) (discA : Discrete A) where
 -- the relation we're interested in
 R : {A B : TypeWithStr ℓ-zero (S A (Discrete→isSet discA))} → (A .fst) → (B .fst) → Type₀
 R {X , memb₁} {Y , memb₂} x y = ∀ a → memb₁ a x ≡ memb₂ a y


 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = ℕ.suc n
 aux a x (no  a≢x) n = n
 
 X = List A
 s : S A (Discrete→isSet discA) X
 s a [] = ℕ.zero
 s a (x ∷ xs) = aux a x (discA a x) (s a xs)
 
 Y = AssocList A
 t : S A (Discrete→isSet discA) Y
 t a ⟨⟩ = ℕ.zero
 t a (⟨ x , ℕ.zero ⟩∷ xs) = t a xs
 t a (⟨ x , ℕ.suc n ⟩∷ xs) = aux a x (discA a x) (t a (⟨ x , n ⟩∷ xs))

 φ : X → Y
 φ [] = ⟨⟩
 φ (x ∷ xs) = ⟨ x , 1 ⟩∷ φ xs

 ψ : Y → X
 ψ ⟨⟩ = []
 ψ (⟨ x , ℕ.zero ⟩∷ xs) = ψ xs
 ψ (⟨ x , ℕ.suc n ⟩∷ xs) = x ∷ ψ (⟨ x , n ⟩∷ xs)

 η : ∀ x → R {X , s} {Y , t} x (φ x)
 η [] a = refl
 η (x ∷ xs) a  with (discA a x)
 ...           | (yes a≡x) = cong ℕ.suc (η xs a)
 ...           | (no  a≢x) = η xs a 

 ε : ∀ y → R {X , s} {Y , t} (ψ y) y
 ε ⟨⟩ a = refl
 ε (⟨ x , ℕ.zero ⟩∷ xs) a = ε xs a
 ε (⟨ x , ℕ.suc n ⟩∷ xs) a = {!!} --aux-aux a x (discA a x)
  where
   aux-aux : (a x : A) → (p : Dec (a ≡ x))
            → aux a x p (s a (ψ (⟨ x , n ⟩∷ xs))) ≡ aux a x p (t a (⟨ x , n ⟩∷ xs))
   aux-aux a x (yes a≡x) = cong ℕ.suc (ε (⟨ x , n ⟩∷ xs) a)
   aux-aux a x (no  a≢x) = ε (⟨ x , n ⟩∷ xs) a
