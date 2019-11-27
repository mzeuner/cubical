{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.SIP where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma.Equivalences

private
 variable
  ℓ ℓ' ℓ'' : Level
 
-- Importing Martin Hötzel-Escardó's structure identity principle into cubical Agda. See
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X, the pair (X , s)
-- means that X is equipped with a S-structure, which is witnessed by s.
-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure.


SNS : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS  {ℓ = ℓ} S ι = ∀ {X : (Type ℓ)} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))


-- Escardo's ρ can actually be  defined from this:
ρ :  {S : Type ℓ → Type ℓ'}
    → {ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''}
    → (SNS S ι)
    → (A : Σ[ X ∈ (Type ℓ) ] (S X)) → (ι A A (idEquiv (A .fst)))
ρ θ A = equivFun (θ (A .snd) (A .snd)) refl

-- We introduce the notation a bit differently:
_≃[_]_ : {S : Type ℓ → Type ℓ'} → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
                           → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (Type (ℓ-max ℓ ℓ''))
A ≃[ ι ] B = Σ[ f ∈ ((A .fst) ≃ (B. fst)) ] (ι A B f)



Id→homEq : (S : Type ℓ → Type ℓ')
          → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
          → (ρ : (A : Σ[ X ∈ (Type ℓ) ] (S X)) → ι A A (idEquiv (A .fst)))
          → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A ≡ B → (A ≃[ ι ] B)
Id→homEq S ι ρ A B p = J (λ y x → A ≃[ ι ] y) (idEquiv (A .fst) , ρ A) p


-- Use a PathP version of Escardó's homomorphism-lemma
hom-lemma-dep : (S : Type ℓ → Type ℓ')
               → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
               → (θ : SNS S ι)
               → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
               → (p : (A .fst) ≡ (B. fst))
               → (PathP (λ i → S (p i)) (A .snd) (B .snd)) ≃ (ι A B (pathToEquiv p))
hom-lemma-dep S ι θ A B p = (J P (λ s → γ s) p) (B .snd)
     where
      P = (λ y x → (s : S y) → PathP (λ i → S (x i)) (A .snd) s ≃ ι A (y , s) (pathToEquiv x))

      γ : (s : S (A .fst)) → ((A .snd) ≡ s) ≃ ι A ((A .fst) , s) (pathToEquiv refl)
      γ s = subst (λ f → ((A .snd) ≡ s) ≃ ι A ((A .fst) , s) f)  (sym pathToEquivRefl) (θ (A. snd) s)


-- Define the inverse of Id→homEq directly.
ua-lemma : (A B : Type ℓ) (e : A ≃ B) → (pathToEquiv (ua e)) ≡ e
ua-lemma A B e = EquivJ (λ b a f →  (pathToEquiv (ua f)) ≡ f)
                       (λ x → subst (λ r → pathToEquiv r ≡ idEquiv x) (sym uaIdEquiv) pathToEquivRefl)
                        B A e
             

homEq→Id : (S : Type ℓ → Type ℓ')
          → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
          → (θ : SNS S ι)
          → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (A ≃[ ι ] B) → A ≡ B
homEq→Id S ι θ A B (f , φ) = ΣPathP (p , q)
        where
         p = ua f

         ψ : ι A B (pathToEquiv p)
         ψ = subst (λ g → ι A B g) (sym (ua-lemma (A .fst) (B. fst) f)) φ
         
         q : PathP (λ i → S (p i)) (A .snd) (B .snd)
         q = equivFun (invEquiv (hom-lemma-dep S ι θ A B p)) ψ


-- Proof of the SIP:
SIP : (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → (θ : SNS S ι)
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A ≡ B) ≃ (A ≃[ ι ] B))
SIP S ι θ A B = 
            (A ≡ B)                                                                 ≃⟨ i ⟩
            (Σ[ p ∈ (A .fst) ≡ (B. fst) ] PathP (λ i → S (p i)) (A .snd) (B .snd))  ≃⟨ ii ⟩
            (Σ[ p ∈ (A .fst) ≡ (B. fst) ] (ι A B (pathToEquiv p)))                  ≃⟨ iii ⟩
            (A ≃[ ι ] B)                                                            ■
    where
     i = invEquiv Σ≡
     ii = Σ-cong-≃ (hom-lemma-dep S ι θ A B)
     iii = Σ-change-of-variable-≃ pathToEquiv (equivIsEquiv univalence)





-- A simple example: pointed types
pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

Pointed-Type : Type (ℓ-suc ℓ)
Pointed-Type {ℓ = ℓ} = Σ (Type ℓ) pointed-structure

pointed-ι : (A B : Pointed-Type) → (A .fst) ≃ (B. fst) → Type ℓ
pointed-ι (X , x) (Y , y) f = (equivFun f) x ≡ y

pointed-is-sns : SNS {ℓ = ℓ} pointed-structure pointed-ι
pointed-is-sns s t = idEquiv (s ≡ t)

pointed-type-sip : (X Y : Type ℓ) (x : X) (y : Y)
                  → (Σ[ f ∈ X ≃ Y ] (f .fst) x ≡ y) ≃ ((X , x) ≡ (Y , y))
pointed-type-sip X Y x y = invEquiv (SIP pointed-structure pointed-ι pointed-is-sns (X , x) (Y , y))
 


-- A new approach using glue types
-- First we define the "push-forward" of an equivalence
_⋆_ : (S : Type ℓ → Type ℓ') → {X Y : Type ℓ} → (X ≃ Y) → (S X ≃ S Y)
S ⋆ f = pathToEquiv (cong S (ua f))

⋆-idEquiv : (S : Type ℓ → Type ℓ') (X : Type ℓ) → (S ⋆ (idEquiv X)) ≡ idEquiv (S X)
⋆-idEquiv S X = (S ⋆ (idEquiv X))  ≡⟨ cong (λ p → pathToEquiv (cong S p)) uaIdEquiv  ⟩
                pathToEquiv refl   ≡⟨ pathToEquivRefl ⟩
                idEquiv (S X)      ∎

-- need a lemma about ua and pathToEquiv that should be in the library
ua-lemma-2 : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-lemma-2 A B p = J (λ b p → ua (pathToEquiv p) ≡ p)
                      ((cong ua (pathToEquivRefl {A = A})) ∙ uaIdEquiv) p

-- a small lemma characterising _⋆_ in Path types
⋆-char : (S : Type ℓ → Type ℓ') (X Y : Type ℓ) (f : X ≃ Y) → ua (S ⋆ f) ≡ cong S (ua f)
⋆-char S X Y f = ua-lemma-2 (S X) (S Y) (cong S (ua f))

PathP-⋆-lemma :(S : Type ℓ → Type ℓ') (A B : Σ[ X ∈ (Type ℓ) ] (S X)) (f : (A .fst) ≃ (B .fst))
               → (PathP (λ i →  ua (S ⋆ f) i) (A .snd) (B .snd)) ≡ (PathP (λ i → S ((ua f) i)) (A .snd) (B .snd))
PathP-⋆-lemma S A B f i = PathP (λ j → (⋆-char S (A .fst) (B .fst) f) i j) (A .snd) (B .snd)
     

-- strong new definition of standard notion of structure.
-- Find something easier later maybe and give a corresponding hom-lemma
SNS' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS'  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → ((equivFun (S ⋆ f)) (A .snd) ≡ (B .snd)) ≃ (ι A B f)


-- a quick sanity-check that our definition is interchangible with Escardó's
SNS'→SNS : (S : Type ℓ → Type ℓ')
          → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
          → (SNS' S ι) → (SNS S ι)
SNS'→SNS {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} S ι θ {X = X} s t = subst (λ x → ((equivFun x) s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X)) (⋆-idEquiv S X) θ-id
  where
   θ-id = θ (X , s) (X , t) (idEquiv X)

SNS→SNS' : (S : Type ℓ → Type ℓ')
          → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
          → (SNS S ι) → (SNS' S ι)
SNS→SNS' {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} S ι θ A B f = (EquivJ P C (B .fst) (A .fst) f) (B .snd) (A .snd)
  where
   P : (X Y : Type ℓ) → Y ≃ X → Type (ℓ-max ℓ' ℓ'')
   P X Y g = (s : S X) (t : S Y) → ((equivFun (S ⋆ g)) t ≡ s) ≃ (ι (Y , t) (X , s) g)

   C : (X : Type ℓ) → (s t : S X) → ((equivFun (S ⋆ (idEquiv X))) t ≡ s) ≃ (ι (X , t) (X , s) (idEquiv X))
   C X s t = subst (λ u →  (u ≡ s) ≃ (ι (X , t) (X , s) (idEquiv X)))
                   (sym ( cong (λ f → (equivFun f) t) (⋆-idEquiv S X))) (θ t s) 


-- Our version of ρ
ρ' : {S : Type ℓ → Type ℓ'}
    → {ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''}
    → (θ : SNS' S ι)
    → (A : Σ[ X ∈ (Type ℓ) ] (S X)) → (ι A A (idEquiv (A .fst)))
ρ' {S = S} {ι = ι} θ A = equivFun (θ A A (idEquiv (A .fst)))
                              (subst (λ f → (f .fst) (A .snd) ≡ (A .snd)) (sym (⋆-idEquiv S (A .fst))) refl)


-- Our version of Id→homEq not using J and ρ' 
pis :  (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → (θ : SNS' S ι)
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (A ≡ B) → (A ≃[ ι ] B)
pis S ι θ A B r = f , equivFun (θ A B f) (λ i → unglue (i ∨ ~ i) (q⋆⋆ i))
   where
    p = λ i → ((r i) .fst)
    f = pathToEquiv p
    q : PathP (λ i → S (p i)) (A .snd) (B .snd)
    q = λ i → ((r i) .snd)
    q⋆ : PathP (λ i → S (ua f i)) (A .snd) (B .snd)
    q⋆ = subst (λ p →  PathP (λ i → S (p i)) (A .snd) (B .snd))
               (sym (ua-lemma-2 (A .fst) (B .fst) p)) q
    q⋆⋆ : PathP (λ i → ua (S ⋆ f) i) (A .snd) (B .snd)
    q⋆⋆ =  transport (λ i → PathP-⋆-lemma S A B f (~ i)) q⋆

--  J (λ b p →  (A ≃[ ι ] b)) (idEquiv (A .fst) , ρ' θ A) r



-- Now we can explicitly construct the inverse:
sip : (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → (θ : SNS' S ι)
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (A ≃[ ι ] B) → A ≡ B
sip S ι θ A B (f , φ) i = p i , q i
   where
    p = ua f
 
    q⋆ : PathP (λ i →  ua (S ⋆ f) i) (A .snd) (B .snd)
    q⋆ i = glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) })
                (equivFun (invEquiv (θ A B f)) φ i)

    q : PathP (λ i → S (p i)) (A .snd) (B .snd)
    q = transport (λ i → PathP-⋆-lemma S A B f i) q⋆



module _(S : Type ℓ → Type ℓ')
        (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
        (θ : SNS' S ι)
        (X Y : Type ℓ)
        (s : S X) (t : S Y)
        (f : X ≃ Y)
        (f-is-ι : ι (X , s) (Y , t) f)                                                where

 p : X ≡ Y
 p = ua f
 
 p⋆ : S X ≡ S Y
 p⋆ = ua (S ⋆ f)
 --  p⋆ = (cong S p) doesn't work since (p⋆ i) would not be a Glue type

 a : equivFun (S ⋆ f) s ≡ t
 a = equivFun (invEquiv (θ (X , s) (Y , t) f)) f-is-ι
 
 q⋆ : PathP (λ i →  p⋆ i) s t
 q⋆ i = glue (λ { (i = i0) → s ; (i = i1) → t })  (a i)

 p⋆-char : p⋆ ≡ cong S p
 p⋆-char = ua-lemma-2 (S X) (S Y) (cong S p)

 PathP-lem : (PathP (λ i → p⋆ i) s t) ≡ (PathP (λ i → S (p i)) s t)
 PathP-lem i = PathP (λ j → p⋆-char i j) s t
 -- cong (λ r →  (PathP (λ i → r i) s t)) p⋆-char
              
 q : PathP (λ i → S (p i)) s t
 q = transport (λ i → PathP-lem i) q⋆ 

 -- sip : (X , s) ≡ (Y , t)
 -- sip i = (p i , q i)
 -- equivFun Σ≡ (p , q)
 
