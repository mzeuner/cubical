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
isZigZagComplete R = ∀ a b a' b' → R a b → R a' b → R a' b' → R a b'

isBisimulation : {A B : Type ℓ} (R : A → B → Type ℓ) (f : A → B) (g : B → A) → Type ℓ
isBisimulation R f g =  isZigZagComplete R
                      × (∀ a → R a (f a))
                      × (∀ b → R (g b) b)

module CarlosThm (A B : Type ℓ) (R : A → B → Type ℓ) (f : A → B) (g : B → A) (isBisRfg : isBisimulation R f g) where
 zigzag : isZigZagComplete R
 zigzag = isBisRfg .fst
 
 α : ∀ a → R a (f a)
 α = isBisRfg .snd .fst
 
 β : ∀ b → R (g b) b
 β = isBisRfg .snd .snd


 Rᴬ : A → A → Type ℓ
 Rᴬ a a' = Σ[ b ∈ B ] (R a b × R a' b)
 
 Rᴮ : B → B → Type ℓ
 Rᴮ b b' = Σ[ a ∈ A ] (R a b × R a b')

 -- Rᴬ and Rᴮ are equivalence relations
 Rᴬ-reflexive : ∀ a → Rᴬ a a
 Rᴬ-reflexive a = f a , α a , α a
 
 Rᴬ-symmetric : ∀ a a' → Rᴬ a a' → Rᴬ a' a
 Rᴬ-symmetric a a' (b , r , s) = b , s , r
 
 Rᴬ-transitive : ∀ a a' a'' → Rᴬ a a' → Rᴬ a' a'' → Rᴬ a a''
 Rᴬ-transitive a a' a'' (b , r , s) (b' , r' , s') = b' , zigzag _ _ _ _ r s r' , s'


 Rᴮ-reflexive : ∀ b → Rᴮ b b
 Rᴮ-reflexive b = g b , β b , β b
 
 Rᴮ-symmetric : ∀ b b' → Rᴮ b b' → Rᴮ b' b
 Rᴮ-symmetric b b' (a , r , s) = a , s , r
 
 Rᴮ-transitive : ∀ b b' b'' → Rᴮ b b' → Rᴮ b' b'' → Rᴮ b b''
 Rᴮ-transitive b b' b'' (a , r , s) (a' , r' , s') = a , r , zigzag _ _ _ _ s r' s'


 -- Now for the proof of A / Rᴬ ≃ B / Rᴮ
 X = A / Rᴬ
 Y = B / Rᴮ

 φ : X → Y
 φ _/_.[ a ] = _/_.[ f a ]
 φ (eq/ a a' r i) = eq/ (f a) (f a') s i
   where
   s : Rᴮ (f a) (f a')
   s = a , α a , zigzag _ _ _ _ (r .snd .fst) (r .snd .snd) (α a')
 φ (squash/ x x₁ p q i j) = squash/ (φ x) (φ x₁) (cong φ p) (cong φ q) i j

 ψ : Y → X
 ψ _/_.[ b ] = _/_.[ g b ]
 ψ (eq/ b b' s i) = eq/ (g b) (g b') r i
  where
  r : Rᴬ (g b) (g b')
  r = b' , zigzag _ _ _ _ (β b) (s .snd .fst) (s .snd .snd) , β b'
 ψ (squash/ y y₁ p q i j) =  squash/ (ψ y) (ψ y₁) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η y = elimProp (λ y → squash/ (φ (ψ y)) y) (λ b → eq/ (f (g b)) b (g b , α (g b) , β b)) y

 ε : retract φ ψ
 ε x = elimProp (λ x → squash/ (ψ (φ x)) x) (λ a → eq/ (g (f a)) a (f a , β (f a) , α a)) x

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
 ...           | yes a≡x = cong ℕ.suc (η xs a)
 ...           | no  a≢x = η xs a 


-- for the other direction we need little helper function
 ε : ∀ y → R {X , s} {Y , t} (ψ y) y
 ε' : (x : A) (n : ℕ) (xs : AssocList A) (a : A) → s a (ψ (⟨ x , n ⟩∷ xs)) ≡ t a (⟨ x , n ⟩∷ xs)

 ε ⟨⟩ a = refl
 ε (⟨ x , n ⟩∷ xs) a = ε' x n xs a

 ε' x ℕ.zero xs a = ε xs a
 ε' x (ℕ.suc n) xs a with discA a x
 ...                 | yes a≡x = cong ℕ.suc (ε' x n xs a)
 ...                 | no  a≢x = ε' x n xs a


 zigzagR : isZigZagComplete (R {X , s} {Y , t})
 zigzagR _ _ _ _ r r' r'' a = (r a) ∙ (r' a) ⁻¹ ∙ (r'' a)
 
 -- Now apply thm 3 
 Rˣ = CarlosThm.Rᴬ X Y (R {X , s} {Y , t}) φ ψ (zigzagR , η , ε)
 Rʸ = CarlosThm.Rᴮ X Y (R {X , s} {Y , t}) φ ψ (zigzagR , η , ε)

 X/Rˣ = CarlosThm.X X Y (R {X , s} {Y , t}) φ ψ (zigzagR , η , ε)
 Y/Rʸ = CarlosThm.Y X Y (R {X , s} {Y , t}) φ ψ (zigzagR , η , ε)

 check1 : X/Rˣ ≡ (X / Rˣ)
 check1 = refl

 check2 : Y/Rʸ ≡ (Y / Rʸ)
 check2 = refl

{- 
We want a commutative square

               ≃
    X/Rˣ  ----------->  Y/Rʸ
     
     |                   |
   ≃ |                   | ≃
     |                   |
     ∨                   ∨
               ≃
  FMSet A  -------->  AList A

We have already established that the vertical arrows are equivalences 
-}

 _∷/_ : A → X/Rˣ → X/Rˣ
 a ∷/ _/_.[ xs ] = _/_.[ a ∷ xs ]
 a ∷/ eq/ xs xs' r i = eq/ (a ∷ xs) (a ∷ xs') r' i
  where
  r' : Rˣ (a ∷ xs) (a ∷ xs')
  r' =  ⟨ a , 1 ⟩∷ (r .fst)
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .fst a'))
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .snd a'))
 a ∷/ squash/ xs xs₁ p q i j = squash/ (a ∷/ xs) (a ∷/ xs₁) (cong (a ∷/_) p) (cong (a ∷/_) q) i j

 infixr 5 _∷/_


 μ : FMSet A → X/Rˣ
 μ = FMS.Rec.f squash/ _/_.[ [] ] _∷/_ α
  where
  α : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
  α a b = elimProp (λ [xs] → squash/ (a ∷/ b ∷/ [xs]) (b ∷/ a ∷/ [xs])) β
   where
   β : ∀ xs → _/_.[ a ∷ b ∷ xs ] ≡ _/_.[ b ∷ a ∷ xs ]
   β xs = eq/ (a ∷ b ∷ xs) (b ∷ a ∷ xs) γ
    where
     γ : Rˣ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
     γ = φ (a ∷ b ∷ xs) , η (a ∷ b ∷ xs) , λ c → δ c ⁻¹ ∙ η (a ∷ b ∷ xs) c
      where
      δ : ∀ c → s c (a ∷ b ∷ xs) ≡ s c (b ∷ a ∷ xs)
      δ c with (discA c a)
      δ c | (yes c≡a)      with (discA c b)
      δ c | (yes c≡a)      | (yes c≡b) = refl
      δ c | (yes c≡a)      | (no  c≢b) = refl
      δ c | (no  c≢a)      with (discA c b)
      δ c | (no  c≢a)      | (yes c≡b) = refl
      δ c | (no  c≢a)      | (no  c≢b) = refl
      


 -- ν : X/Rˣ → FMSet A
 -- ν _/_.[ [] ] = []
 -- ν _/_.[ x ∷ xs ] = x ∷ ν _/_.[ xs ]
 -- ν (eq/ xs xs' r i) = {!!}
 --  where
 --   ρ : ∀ a → s a xs ≡ s a xs'
 --   ρ = λ a → (r .snd .fst a) ∙ (r .snd .snd a) ⁻¹
 -- ν (squash/ xs/ xs/' p q i j) = trunc (ν xs/) (ν xs/') (cong ν p) (cong ν q) i j
