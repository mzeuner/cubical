{-# OPTIONS --cubical #-}
module Cubical.HITs.SetQuotients.ZigZagRel where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma using (_×_; ΣProp≡)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Empty as ⊥
open import Cubical.Structures.MultiSet renaming (member-structure to S; member-iso to ι; Member-is-SNS to SNS[S,ι])
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
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
 φ [ a ] = [ f a ]
 φ (eq/ a a' r i) = eq/ (f a) (f a') s i
   where
   s : Rᴮ (f a) (f a')
   s = a , α a , zigzag _ _ _ _ (r .snd .fst) (r .snd .snd) (α a')
 φ (squash/ x x₁ p q i j) = squash/ (φ x) (φ x₁) (cong φ p) (cong φ q) i j

 ψ : Y → X
 ψ [ b ] = [ g b ]
 ψ (eq/ b b' s i) = eq/ (g b) (g b') r i
  where
  r : Rᴬ (g b) (g b')
  r = b' , zigzag _ _ _ _ (β b) (s .snd .fst) (s .snd .snd) , β b'
 ψ (squash/ y y₁ p q i j) =  squash/ (ψ y) (ψ y₁) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η y = elimProp (λ y → squash/ (φ (ψ y)) y) (λ b → eq/ _ _ (g b , α (g b) , β b)) y

 ε : retract φ ψ
 ε x = elimProp (λ x → squash/ (ψ (φ x)) x) (λ a → eq/ _ _ (f a , β (f a) , α a)) x

 Thm3 : X ≃ Y
 Thm3 = isoToEquiv (iso φ ψ η ε)


-- Now for the applications:
-- defining association lists without higher constructors
data AssocList (A : Type₀) : Type₀ where
 ⟪⟫ : AssocList A
 ⟪_,_⟫∷_ : A → ℕ → AssocList A → AssocList A

infixr 5 ⟪_,_⟫∷_

module _(A : Type₀) (discA : Discrete A) where
 -- the relation we're interested in
 R : {A B : TypeWithStr ℓ-zero (S A (Discrete→isSet discA))} → (A .fst) → (B .fst) → Type₀
 R {X , memb₁} {Y , memb₂} x y = ∀ a → memb₁ a x ≡ memb₂ a y


 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n

 X = List A
 s : S A (Discrete→isSet discA) X
 s a [] = zero
 s a (x ∷ xs) = aux a x (discA a x) (s a xs)

 Y = AssocList A
 t : S A (Discrete→isSet discA) Y
 t a ⟪⟫ = zero
 t a (⟪ x , zero ⟫∷ xs) = t a xs
 t a (⟪ x , suc n ⟫∷ xs) = aux a x (discA a x) (t a (⟪ x , n ⟫∷ xs))

 φ : X → Y
 φ [] = ⟪⟫
 φ (x ∷ xs) = ⟪ x , 1 ⟫∷ φ xs

 ψ : Y → X
 ψ ⟪⟫ = []
 ψ (⟪ x , zero ⟫∷ xs) = ψ xs
 ψ (⟪ x , suc n ⟫∷ xs) = x ∷ ψ (⟪ x , n ⟫∷ xs)

 η : ∀ x → R {X , s} {Y , t} x (φ x)
 η [] a = refl
 η (x ∷ xs) a  with (discA a x)
 ...           | yes a≡x = cong suc (η xs a)
 ...           | no  a≢x = η xs a


-- for the other direction we need little helper function
 ε : ∀ y → R {X , s} {Y , t} (ψ y) y
 ε' : (x : A) (n : ℕ) (xs : AssocList A) (a : A)
    → s a (ψ (⟪ x , n ⟫∷ xs)) ≡ t a (⟪ x , n ⟫∷ xs)

 ε ⟪⟫ a = refl
 ε (⟪ x , n ⟫∷ xs) a = ε' x n xs a

 ε' x zero xs a = ε xs a
 ε' x (suc n) xs a with discA a x
 ...                 | yes a≡x = cong suc (ε' x n xs a)
 ...                 | no  a≢x = ε' x n xs a


 zigzagR : isZigZagComplete (R {X , s} {Y , t})
 zigzagR _ _ _ _ r r' r'' a = (r a) ∙∙ (r' a) ⁻¹ ∙∙ (r'' a)

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

We have already established that the horizontal arrows are equivalences
-}

 _∷/_ : A → X/Rˣ → X/Rˣ
 a ∷/ [ xs ] = [ a ∷ xs ]
 a ∷/ eq/ xs xs' r i = eq/ (a ∷ xs) (a ∷ xs') r' i
  where
  r' : Rˣ (a ∷ xs) (a ∷ xs')
  r' =  ⟪ a , 1 ⟫∷ (r .fst)
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .fst a'))
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .snd a'))
 a ∷/ squash/ xs xs₁ p q i j = squash/ (a ∷/ xs) (a ∷/ xs₁) (cong (a ∷/_) p) (cong (a ∷/_) q) i j

 infixr 5 _∷/_


 μ : FMSet A → X/Rˣ
 μ = FMS.Rec.f squash/ [ [] ] _∷/_ β
  where
  β : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
  β a b = elimProp (λ _ → squash/ _ _) (λ xs → eq/ _ _ (γ xs))
   where
     γ : ∀ xs → Rˣ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
     γ xs = φ (a ∷ b ∷ xs) , η (a ∷ b ∷ xs) , λ c → δ c ⁻¹ ∙ η (a ∷ b ∷ xs) c
      where
      δ : ∀ c → s c (a ∷ b ∷ xs) ≡ s c (b ∷ a ∷ xs)
      δ c with discA c a | discA c b
      δ c | yes _        | yes _ = refl
      δ c | yes _        | no  _ = refl
      δ c | no  _        | yes _ = refl
      δ c | no  _        | no  _ = refl










 --for the inverse we need some lemmas
 FMScount : A → FMSet A → ℕ
 FMScount = FMSmember discA

 FMScount-lemma : ∀ x xs → FMScount x (x ∷ xs) ≡ suc (FMScount x xs)
 FMScount-lemma x xs with discA x x
 ...                 | yes _  = refl
 ...                 | no  x≢x = ⊥.rec (x≢x refl)

 FMScount-0-lemma : ∀ xs → (∀ a → FMScount a xs ≡ 0) → xs ≡ []
 FMScount-0-lemma = FMS.ElimProp.f (isPropΠ λ _ → FMS.trunc _ _) (λ _ → refl) θ
  where
  θ : ∀ x {xs} → ((∀ a → FMScount a xs ≡ 0) → xs ≡ [])
               → ((∀ a → FMScount a (x ∷ xs) ≡ 0) → (x FMS.∷ xs) ≡ [])
  θ x {xs} _ p = ⊥.rec (snotz (path ∙ p x))
   where
   path : suc (FMScount x xs) ≡ FMScount x (x ∷ xs)
   path with discA x x
   path | yes _ = refl
   path | no x≢x = ⊥.rec (x≢x refl)

 FMScount-0-lemma-sym : ∀ xs → (∀ a → 0 ≡ FMScount a xs) → [] ≡ xs
 FMScount-0-lemma-sym xs p = sym (FMScount-0-lemma xs λ a → sym (p a))



 -- removes a completely...
 -- remove-aux : (a x : A) → FMSet A → Dec (a ≡ x) → FMSet A
 -- remove-aux a x xs (yes _) = xs
 -- remove-aux a x xs (no  _) = x ∷ xs

 -- remove-∷* : (a x : A) → FMSet A → FMSet A
 -- remove-∷* a x xs = remove-aux a x xs (discA a x)

 -- remove-comm*-aux : (a x y : A) (xs : FMSet A)
 --                    (p : Dec (a ≡ x)) (q : Dec (a ≡ y))
 --                  → remove-aux a x (remove-aux a y xs q) p
 --                  ≡ remove-aux a y (remove-aux a x xs p) q
 -- remove-comm*-aux a x y xs (yes _) (yes _) = refl
 -- remove-comm*-aux a x y xs (yes _) (no  _) = refl
 -- remove-comm*-aux a x y xs (no  _) (yes _) = refl
 -- remove-comm*-aux a x y xs (no  _) (no  _) = comm x y xs

 -- remove-comm* : (a x y : A) (xs : FMSet A)
 --              → remove-∷* a x (remove-∷* a y xs)
 --              ≡ remove-∷* a y (remove-∷* a x xs)
 -- remove-comm* a x y xs = remove-comm*-aux a x y xs (discA a x) (discA a y)

 -- remove : A → FMSet A → FMSet A
 -- remove a = FMS.Rec.f FMS.trunc [] (remove-∷* a) (remove-comm* a)

 -- remove-lemma : ∀ a xs → FMScount a (remove a xs) ≡ zero
 -- remove-lemma a = FMS.ElimProp.f (isSetℕ _ _) refl θ
 --  where
 --  ρ : (x : A) (xs : FMSet A) (p : Dec (a ≡ x))
 --    → FMScount a xs ≡ zero
 --    → FMScount a (remove-aux a x xs p) ≡ zero
 --  ρ x xs (yes _)  q = q
 --  ρ x xs (no a≢x) q with (discA a x)
 --  ...              | yes a≡x = ⊥.rec (a≢x a≡x)
 --  ...              | no _    = q
 --  -- can't use with in def of θ for some reason
 --  θ : (x : A) {xs : FMSet A}
 --    → FMScount a (remove a xs) ≡ zero
 --    → FMScount a (remove a (x ∷ xs)) ≡ zero
 --  θ x {xs} q = ρ x (remove a xs) (discA a x) q


 -- remove-lemma2 : ∀ a xs → xs ≡ multi-∷ a (FMScount a xs) (remove a xs)
 -- remove-lemma2 a = FMS.ElimProp.f (FMS.trunc _ _) refl θ
 --  where
 --  ρ : (x : A) (xs ys : FMSet A) (p : Dec (a ≡ x))
 --    → ys ≡ multi-∷ a (FMScount a ys) xs
 --    → x ∷ ys ≡ multi-∷ a (FMScount a (x ∷ ys)) (remove-aux a x xs p)
 --  ρ x xs ys (yes a≡x) q with discA a x
 --  ρ x xs ys (yes a≡x) q | yes _   = cong (_∷ ys) a≡x ⁻¹ ∙ cong (a ∷_) q
 --  ρ x xs ys (yes a≡x) q | no  a≢x = ⊥.rec (a≢x a≡x)
 --  ρ x xs ys (no  a≢x) q with discA a x
 --  ρ x xs ys (no  a≢x) q | yes a≡x = ⊥.rec (a≢x a≡x)
 --  ρ x xs ys (no  a≢x) q | no  _   = cong (x ∷_) q ∙ eq' x a (FMScount a ys) xs
 --   where
 --   eq' : ∀ x y n xs → x ∷ multi-∷ y n xs ≡ multi-∷ y n (x ∷ xs)
 --   eq' x y zero xs = refl
 --   eq' x y (suc n) xs = comm x y (multi-∷ y n xs) ∙ cong (y ∷_) (eq' x y n xs)
 --  -- can't use with in def of θ for some reason
 --  θ : ∀ x {xs} → xs ≡ multi-∷ a (FMScount a xs) (remove a xs)
 --               → x ∷ xs ≡ multi-∷ a (FMScount a (x ∷ xs)) (remove a (x ∷ xs))
 --  θ x {xs} q = ρ x (remove a xs) xs (discA a x) q




 -- for removing a once
 remove1 : A → FMSet A → FMSet A
 remove1 a [] = []
 remove1 a (x ∷ xs) with (discA a x)
 ...               | yes _ = xs
 ...               | no  _ = x ∷ remove1 a xs
 remove1 a (comm x y xs i) = path i
  where
  path : remove1 a (x ∷ y ∷ xs) ≡ remove1 a (y ∷ x ∷ xs)
  path with discA a x with discA a y
  path | yes a≡x      | yes a≡y = λ i → ((a≡y ⁻¹ ∙ a≡x) i) ∷ xs
  path | yes a≡x      | no  _   = λ i → y ∷ (eq' i)
   where
   eq' : xs ≡ remove1 a (x ∷ xs)
   eq' with discA a x
   eq' | yes _   = refl
   eq' | no  a≢x = ⊥.rec (a≢x a≡x)

  path | no  _        | yes a≡y = λ i → x ∷ (eq' i)
   where
   eq' : remove1 a (y ∷ xs) ≡ xs
   eq' with discA a y
   eq' | yes _   = refl
   eq' | no  a≢y = ⊥.rec (a≢y a≡y)

  path | no  a≢x      | no  a≢y = (λ i → x ∷ (p i)) ∙∙ comm x y (remove1 a xs) ∙∙ (λ i → y ∷ (sym q i))
   where
   p : remove1 a (y ∷ xs) ≡ y ∷ (remove1 a xs)
   p with discA a y
   p | yes a≡y = ⊥.rec (a≢y a≡y)
   p | no  _   = refl

   q : remove1 a (x ∷ xs) ≡ x ∷ (remove1 a xs)
   q with discA a x
   q | yes a≡x = ⊥.rec (a≢x a≡x)
   q | no  _   = refl

 remove1 a (trunc xs ys p q i j) = trunc (remove1 a xs) (remove1 a ys) (cong (remove1 a) p) (cong (remove1 a) q) i j



 lem-remove1 : ∀ a xs → FMScount a (remove1 a xs) ≡ predℕ (FMScount a xs)
 lem-remove1 a = FMS.ElimProp.f (isSetℕ _ _) refl θ
  where
  θ : ∀ x {xs} → FMScount a (remove1 a xs) ≡ predℕ (FMScount a xs)
               → FMScount a (remove1 a (x ∷ xs)) ≡ predℕ (FMScount a (x ∷ xs))
  θ x {xs} p with discA a x
  ...        | yes a≡x = refl
  ...        | no  a≢x = path ∙ p
   where
   path : FMScount a (x ∷ (remove1 a xs)) ≡ FMScount a (remove1 a xs)
   path with discA a x
   path | yes a≡x = ⊥.rec (a≢x a≡x)
   path | no  a≢x = refl


 remove1-lemma-zero : ∀ a xs → FMScount a xs ≡ zero → xs ≡ remove1 a xs
 remove1-lemma-zero a = FMS.ElimProp.f (isPropΠ λ _ → FMS.trunc _ _) (λ _ → refl) θ
  where
  θ : ∀ x {xs} → (FMScount a xs ≡ zero → xs ≡ remove1 a xs)
               → FMScount a (x ∷ xs) ≡ zero → x ∷ xs ≡ remove1 a (x ∷ xs)
  θ x {xs} hyp p with discA a x
  ...            | yes _ = ⊥.rec (snotz p)
  ...            | no  _ = cong (x ∷_) (hyp p)


 remove1-lemma-suc : ∀ a n xs → FMScount a xs ≡ suc n → xs ≡ a ∷ (remove1 a xs)
 remove1-lemma-suc a n = FMS.ElimProp.f (isPropΠ λ _ → FMS.trunc _ _) (λ p → ⊥.rec (znots p)) θ
  where
  θ : ∀ x {xs} → (FMScount a xs ≡ suc n → xs ≡ a ∷ (remove1 a xs))
               → FMScount a (x ∷ xs) ≡ suc n → x ∷ xs ≡ a ∷ (remove1 a (x ∷ xs))
  θ x {xs} hyp p with discA a x
  ...            | yes a≡x = (λ i → (sym a≡x i) ∷ xs) ∙ (λ i → a ∷ (path i))
   where
   path : xs ≡ remove1 a (x ∷ xs)
   path with discA a x
   path | yes _   = refl
   path | no  a≢x = ⊥.rec (a≢x a≡x)

  ...            | no  a≢x = cong (x ∷_) (hyp p) ∙∙ comm x a (remove1 a xs) ∙∙ (λ i → a ∷ (path i))
   where
   path : x ∷ (remove1 a xs) ≡ remove1 a (x ∷ xs)
   path with discA a x
   path | yes a≡x = ⊥.rec (a≢x a≡x)
   path | no  _   = refl


 -- generalizing ElimProp
 _≼_ : FMSet A → FMSet A → Type₀ --\preceq
 xs ≼ ys = ∀ a → FMScount a xs ≤ FMScount a ys

 ≼-refl : ∀ xs → xs ≼ xs
 ≼-refl xs a  = ≤-refl
 
 -- Where to move this? Has to come after definition of FMSmember!
 -- FMS-≼-ElimPropf : ∀ {ℓ} {B : FMSet A → Type ℓ}
 --                 → (∀ {xs} → isProp (B xs))
 --                 → B []
 --                 → (∀ x xs → (∀ ys → ys ≼ xs → B ys) → B (x ∷ xs))
 --                 ---------------------------------------------------
 --                 → (∀ xs → B xs)
 -- FMS-≼-ElimPropf {ℓ = ℓ} {B = B} Bprop b₀ hyp = FMS.ElimProp.f Bprop b₀ θ
 --  where
 --  θ : ∀ x {xs} → B xs → B (x ∷ xs)
 --  θ x {xs} b = hyp x xs {!!}

 -- prove that later, looks correct
 postulate
  FMS-≼-ElimPropBin :  ∀ {ℓ} {B : FMSet A → FMSet A → Type ℓ}
                    → (∀ {xs} {ys} → isProp (B xs ys))
                    → (∀ xs → B xs [])
                    → (∀ ys → B [] ys)
                    → (∀ x y xs ys → (∀ vs ws → vs ≼ xs → ws ≼ ys → B vs ws) → B (x ∷ xs) (y ∷ ys))
                    -------------------------------------------------------------------------------
                    → (∀ xs ys → B xs ys)
                       

--- some results about ℕ, move that for PR ------------------------------------------------------------------------------
 ≤-predℕ : ∀ n → predℕ n ≤ n
 ≤-predℕ zero = ≤-refl
 ≤-predℕ (suc n) = ≤-suc ≤-refl

 suc-predℕ : ∀ n → ¬ n ≡ 0 → n ≡ suc (predℕ n)
 suc-predℕ zero p = ⊥.rec (p refl)
 suc-predℕ (suc n) p = refl
------------------------------------------------------------------------------------------------------------------------ 


 ≼-remove1 : ∀ a xs → remove1 a xs ≼ xs
 ≼-remove1 a xs b with discA a b
 ...              | yes a≡b = subst (λ n → n ≤ FMScount b xs) (path ⁻¹) (≤-predℕ (FMScount b xs))
  where
  path : FMScount b (remove1 a xs) ≡ predℕ (FMScount b xs)
  path = cong (λ c → FMScount b (remove1 c xs)) a≡b ∙ lem-remove1 b xs
 ...              | no  a≢b = subst (λ n → n ≤ FMScount b xs) (path ⁻¹) ≤-refl
  where
  path : FMScount b (remove1 a xs) ≡ FMScount b xs
  path with discreteℕ (FMScount a xs) zero
  path | yes p = cong (FMScount b) (remove1-lemma-zero a xs p ⁻¹)
  path | no ¬p = eq₁ (remove1 a xs) ∙ cong (FMScount b) eq₂
   where
   eq₁ : ∀ ys → FMScount b ys ≡ FMScount b (a ∷ ys)
   eq₁ ys with discA b a
   ...    | yes b≡a = ⊥.rec (a≢b (b≡a ⁻¹))
   ...    | no  _   = refl
   eq₂ : (a ∷ remove1 a xs) ≡ xs
   eq₂ = remove1-lemma-suc a (predℕ (FMScount a xs)) xs (suc-predℕ (FMScount a xs) ¬p) ⁻¹



 -- The main result:
 FMScountExt : ∀ xs xs' → (∀ a → FMScount a xs ≡ FMScount a xs') → xs ≡ xs'
 FMScountExt = FMS-≼-ElimPropBin (isPropΠ λ _ → FMS.trunc _ _) FMScount-0-lemma FMScount-0-lemma-sym θ
  where
  θ :  ∀ x y xs ys
    → (∀ vs ws → vs ≼ xs → ws ≼ ys → (∀ a → FMScount a vs ≡ FMScount a ws) → vs ≡ ws)
    → (∀ a → FMScount a (x ∷ xs) ≡ FMScount a (y ∷ ys))
    ---------------------------------------------------------------------------------
    → x FMS.∷ xs ≡ y FMS.∷ ys
  θ x y xs ys ≼-hyp count-hyp with discA x y
  -- in the case that x≡y we apply the induction hypothesis on xs and ys
  ...                         | yes x≡y = cong (_∷ xs) x≡y ∙ (λ i → y ∷ path i)
   where 
   path : xs ≡ ys
   path = ≼-hyp xs ys (≼-refl xs) (≼-refl ys) count-eq
       where
       count-eq : ∀ a → FMScount a xs ≡ FMScount a ys
       count-eq a with discA a x with discA a y
       ...        | yes a≡x      | yes a≡y = cong predℕ (eq₁ ∙∙ (count-hyp a) ∙∙ eq₂ ⁻¹)
        where
        eq₁ : suc (FMScount a xs) ≡ FMScount a (x ∷ xs)
        eq₁ with discA a x
        eq₁ | yes _   = refl
        eq₁ | no  a≢x = ⊥.rec (a≢x a≡x)

        eq₂ : suc (FMScount a ys) ≡ FMScount a (y ∷ ys)
        eq₂ with discA a y
        eq₂ | yes _    = refl
        eq₂ | no  a≢y  = ⊥.rec (a≢y a≡y)
       ...        | yes a≡x      | no  a≢y = ⊥.rec (a≢y (a≡x ∙ x≡y))
       ...        | no  a≢x      | yes a≡y = ⊥.rec (a≢x (a≡y ∙ x≡y ⁻¹))
       ...        | no  a≢x      | no  a≢y = eq₁ ∙∙ (count-hyp a) ∙∙ eq₂ ⁻¹
        where
        eq₁ : FMScount a xs ≡ FMScount a (x ∷ xs)
        eq₁ with discA a x
        eq₁ | yes a≡x = ⊥.rec (a≢x a≡x)
        eq₁ | no  _   = refl

        eq₂ : FMScount a ys ≡ FMScount a (y ∷ ys)
        eq₂ with discA a y
        eq₂ | yes a≡y = ⊥.rec (a≢y a≡y)
        eq₂ | no  _   = refl
   
  -- in the case that x≢y we apply the induction hypothesis on (remove1 y xs) and (remove1 x ys) 
  ...                         | no  x≢y = x ∷ xs                 ≡⟨ cong (x ∷_) path₁ ⟩
                                          x ∷ y ∷ (remove1 y xs) ≡⟨ (λ i → x ∷ y ∷ (hyp-path i)) ⟩
                                          x ∷ y ∷ (remove1 x ys) ≡⟨ comm x y (remove1 x ys) ⟩
                                          y ∷ x ∷ (remove1 x ys) ≡⟨ cong (y ∷_) path₂ ⁻¹ ⟩
                                          y ∷ ys                 ∎
   where   
   eq₁ : FMScount y xs ≡ suc (FMScount y ys)
   eq₁ = p ∙∙ count-hyp y ∙∙ FMScount-lemma y ys
    where
    p : FMScount y xs ≡ FMScount y (x ∷ xs)
    p with discA y x
    p | yes y≡x = ⊥.rec (x≢y (y≡x ⁻¹))
    p | no  _   = refl
   
   eq₂ : FMScount x ys ≡ suc (FMScount x xs)
   eq₂ = p ∙∙ count-hyp x ⁻¹ ∙∙ FMScount-lemma x xs
    where
    p : FMScount x ys ≡ FMScount x (y ∷ ys)
    p with discA x y
    p | yes x≡y = ⊥.rec (x≢y x≡y)
    p | no  _   = refl
   
   path₁ : xs ≡ y ∷ (remove1 y xs)
   path₁ = remove1-lemma-suc y (FMScount y ys) xs eq₁
   
   path₂ : ys ≡ x ∷ (remove1 x ys)
   path₂ = remove1-lemma-suc x (FMScount x xs) ys eq₂

   vs = remove1 y xs
   ws = remove1 x ys
   
   hyp-path : vs ≡ ws
   hyp-path = ≼-hyp vs ws (≼-remove1 y xs) (≼-remove1 x ys) χ
    where
    χ : ∀ a → FMScount a vs ≡ FMScount a ws
    χ a with discA a x with discA a y
    ... | yes a≡x      | yes a≡y = ⊥.rec (x≢y (a≡x ⁻¹ ∙ a≡y))
    ... | yes a≡x      | no  a≢y = FMScount a vs               ≡⟨ {!!} ⟩
                                   FMScount a xs               ≡⟨ {!!} ⟩
                                   predℕ (FMScount a (x ∷ xs)) ≡⟨ {!!} ⟩
                                   predℕ (FMScount a (y ∷ ys)) ≡⟨ {!!} ⟩
                                   predℕ (FMScount a ys)       ≡⟨ {!!} ⟩
                                   FMScount a ws               ∎
    ... | no  a≢x      | yes a≡y = FMScount a vs               ≡⟨ {!!} ⟩
                                   predℕ (FMScount a xs)       ≡⟨ {!!} ⟩
                                   predℕ (FMScount a (x ∷ xs)) ≡⟨ {!!} ⟩
                                   predℕ (FMScount a (y ∷ ys)) ≡⟨ {!!} ⟩
                                   FMScount a ys               ≡⟨ {!!} ⟩
                                   FMScount a ws               ∎
    ... | no  a≢x      | no  a≢y = FMScount a vs               ≡⟨ {!!} ⟩
                                   FMScount a xs               ≡⟨ {!!} ⟩
                                   FMScount a (x ∷ xs)         ≡⟨ {!!} ⟩
                                   FMScount a (y ∷ ys)         ≡⟨ {!!} ⟩
                                   FMScount a ys               ≡⟨ {!!} ⟩
                                   FMScount a ws               ∎





 -- ν : X/Rˣ → FMSet A
 -- ν [ [] ] = []
 -- ν [ x ∷ xs ] = x ∷ ν [ xs ]
 -- ν (eq/ xs xs' r i) = {!!}
 --  where
 --   ρ : ∀ a → s a xs ≡ s a xs'
 --   ρ = λ a → (r .snd .fst a) ∙ (r .snd .snd a) ⁻¹
 -- ν (squash/ xs/ xs/' p q i j) = trunc (ν xs/) (ν xs/') (cong ν p) (cong ν q) i j





















 -- We want to construct a function Y/Rʸ → AList A,
 -- for that we have to prove that every association list is determined by the of ALmember
 -- count = ALmember discA

 -- lem : (a : A) (n : ℕ) (xs : AList A) → count a (⟨ a , n ⟩∷ xs) ≡ n + count a xs
 -- lem a n xs with discA a a
 -- lem a n xs | yes _  = refl
 -- lem a n xs | no a≢a = ⊥.rec (a≢a refl)

 -- lemma : (xs : AList A) → (∀ a → count a xs ≡ 0) → xs ≡ ⟨⟩
 -- lemma = AL.ElimProp.f (λ {xs} → isPropΠ λ _ → AL.trunc xs ⟨⟩) (λ _ → refl) (λ b n {xs} → ρ b n xs)
 --  where
 --  ρ : ∀ b n xs → ((∀ a → count a xs ≡ 0) → xs ≡ ⟨⟩)
 --               → (∀ a → count a (⟨ b , n ⟩∷ xs) ≡ 0) → (⟨ b , n ⟩∷ xs) ≡ AL.⟨⟩
 --  ρ b zero xs β γ = del b xs ∙ β δ
 --   where
 --   δ : ∀ a → count a xs ≡ 0
 --   δ a = cong (count a) (del b xs ⁻¹) ∙ γ a
 --  ρ b (suc n) xs β γ = ⊥.rec (znots (γ b ⁻¹ ∙ lem b (suc n) xs))

 -- -- AL-safetail : AList A → AList A
 -- -- AL-safetail = AL.Rec.f AL.trunc ⟨⟩ (λ _ _ xs → xs) (λ _ _ _ → refl) (λ _ _ _ _ → refl) λ _ _ → refl

 -- -- AL-safetail-lem : ∀ a n xs → AL-safetail (⟨ a , n ⟩∷ xs) ≡ xs
 -- -- AL-safetail-lem a n xs = {!refl!} -- AL.ElimProp.f (λ {xs} → AL.trunc _ _) refl λ b m {xs} → ρ b m xs
 -- --  -- where
 -- --  -- ρ : ∀ b m xs → AL-safetail (⟨ a , n ⟩∷ xs) ≡ xs
 -- --  --              → AL-safetail (⟨ a , n ⟩∷ ⟨ b , m ⟩∷ xs) ≡ ⟨ b , m ⟩∷ xs
 -- --  -- ρ b m xs p = {!!}


 -- cancel-lemma1 : {a : A} {xs ys : AList A} → ⟨ a , 1 ⟩∷ xs ≡ ⟨ a , 1 ⟩∷ ys → xs ≡ ys
 -- cancel-lemma1 {a} {xs} {ys} p = {!!}
 -- --AL-safetail-lem a 1 xs ⁻¹ ∙∙ cong AL-safetail p ∙∙ AL-safetail-lem a 1 ys

 -- cancel-lemma : (a : A) (n : ℕ) (xs ys : AList A) → ⟨ a , n ⟩∷ xs ≡ ⟨ a , n ⟩∷ ys
 --                                                  → xs ≡ ys
 -- cancel-lemma a zero xs ys p = del a xs ⁻¹ ∙∙ p ∙∙ del a ys
 -- cancel-lemma a (suc n) xs ys p = cancel-lemma a n xs ys
 --                                 (cancel-lemma1 (agg a 1 n xs ∙∙ p ∙∙ agg a 1 n ys ⁻¹))



 -- T : A → AList A → Type₀
 -- T a xs = Σ[ ys ∈ AList A ] xs ≡ ⟨ a , count a xs ⟩∷ ys


 -- Thm1 : (a : A) (xs : AList A) → isContr (T a xs)
 -- Thm1 a = AL.ElimProp.f isPropIsContr (α , α≡) λ b n {xs} κ → ρ b n xs κ
 --  where
 --  α : T a ⟨⟩
 --  α = ⟨⟩ , del a ⟨⟩ ⁻¹

 --  α≡ : (β : T a ⟨⟩) → α ≡ β
 --  α≡ β = ΣProp≡ (λ _ → AL.trunc _ _) (β .snd ∙ del a (β .fst))

 --  ρ : (b : A) (n : ℕ) (xs : AList A) → isContr (T a xs)
 --                                     → isContr (T a (⟨ b , n ⟩∷ xs))
 --  ρ b n xs ((ys , p) , r) = γ , γ≡
 --   where
 --   γ : T a (⟨ b , n ⟩∷ xs)
 --   γ with discA a b
 --   γ | yes a≡b = ys , (cong (⟨ b , n ⟩∷_) p)
 --                    ∙∙ subst (λ c → ⟨ b , n ⟩∷ ⟨ a , (count a xs) ⟩∷ ys ≡ ⟨ c , n ⟩∷ ⟨ a , (count a xs) ⟩∷ ys)
 --                             (a≡b ⁻¹) refl
 --                    ∙∙ agg a n (count a xs) ys
 --   γ | no a≢b = ⟨ b , n ⟩∷ ys , (cong (⟨ b , n ⟩∷_) p) ∙ multiPer b a n (count a xs) ys
 --    where
 --    eq' : count a (⟨ b , n ⟩∷ ys) ≡ count a ys
 --    eq' with discA a b
 --    eq' | yes a≡b = ⊥.rec (a≢b a≡b)
 --    eq' | no _ = refl

 --   γ≡ : (β : T a (⟨ b , n ⟩∷ xs)) → γ ≡ β
 --   γ≡ β = ΣProp≡ (λ _ → AL.trunc _ _) (cancel-lemma a (count a (⟨ b , n ⟩∷ xs)) (γ .fst) (β .fst) (γ .snd ⁻¹ ∙ β .snd))
 --   -- can we do without cancel-lemma?


 -- Thm2 : (xs' xs : AList A) → (∀ a → count a xs' ≡ count a xs) → xs' ≡ xs
 -- Thm2 xs' = AL.ElimProp.f (λ {xs} → isPropΠ λ _ → AL.trunc xs' xs) (lemma xs') λ b n {xs} no h → ρ b n xs no h
 --  where
 --  ρ : (b : A) (n : ℕ) (xs : AList A)
 --    → ((∀ a → count a xs' ≡ count a xs) → xs' ≡ xs)
 --    → (∀ a → count a xs' ≡ count a (⟨ b , n ⟩∷ xs))
 --    → xs' ≡ ⟨ b , n ⟩∷ xs
 --  ρ b n xs _ κ = xs'                               ≡⟨ q' ⟩
 --                 ⟨ b , count b xs' ⟩∷ ys'          ≡⟨ (λ i → ⟨ b , count b xs' ⟩∷ (eq' i)) ⟩
 --                 ⟨ b , count b xs' ⟩∷ ys           ≡⟨ (λ i → ⟨ b , (foo i) ⟩∷ ys) ⟩
 --                 ⟨ b , n + count b xs ⟩∷ ys        ≡⟨ agg b n (count b xs) ys ⁻¹ ⟩
 --                 ⟨ b , n ⟩∷ ⟨ b , count b xs ⟩∷ ys ≡⟨ cong (⟨ b , n ⟩∷_) (q ⁻¹) ⟩
 --                 ⟨ b , n ⟩∷ xs                     ∎
 --   where
 --   α = Thm1 b xs .fst
 --   ys = α .fst
 --   p = α .snd .fst
 --   q = α .snd .snd

 --   β = Thm1 b xs' .fst
 --   ys' = β .fst
 --   p' = β .snd .fst
 --   q' = β .snd .snd

 --   foo : count b xs' ≡ n + count b xs
 --   foo = κ b ∙ lem b n xs

 --   eq' : ys' ≡ ys
 --   eq' = {!!} --Thm2 ys' ys ? makes termination check fail
