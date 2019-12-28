{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.cubicalSIP where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma.Equivalences
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)


private
 variable
  ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
 
-- In this file we apply the cubical machinery to Martin Hötzel-Escardó's structure identity principle
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X, the pair (X , s)
-- means that X is equipped with a S-structure, which is witnessed by s.
-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.

-- throughout we will use that ua and pathToEquiv are mutually inverse:
ua-lemma : (A B : Type ℓ) (e : A ≃ B) → (pathToEquiv (ua e)) ≡ e
ua-lemma A B e = EquivJ (λ b a f →  (pathToEquiv (ua f)) ≡ f)
                       (λ x → subst (λ r → pathToEquiv r ≡ idEquiv x) (sym uaIdEquiv) pathToEquivRefl)
                        B A e

ua-lemma-2 : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-lemma-2 A B p = J (λ b p → ua (pathToEquiv p) ≡ p)
                      ((cong ua (pathToEquivRefl {A = A})) ∙ uaIdEquiv) p
            


-- original (slightly modified) definition of SNS:
SNS : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS  {ℓ = ℓ} S ι = ∀ {X : (Type ℓ)} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))

-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : {S : Type ℓ → Type ℓ'} → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
                           → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (Type (ℓ-max ℓ ℓ''))
A ≃[ ι ] B = Σ[ f ∈ ((A .fst) ≃ (B. fst)) ] (ι A B f)



-- Before we can formulate our version of an SNS we have to introduce a bit of notation
-- and prove a few basic results.
-- First, we define the "cong-≃":
_⋆_ : (S : Type ℓ → Type ℓ') → {X Y : Type ℓ} → (X ≃ Y) → (S X ≃ S Y)
S ⋆ f = pathToEquiv (cong S (ua f))


-- Next, we prove a couple of helpful results about this ⋆ opreation:
⋆-idEquiv : (S : Type ℓ → Type ℓ') (X : Type ℓ) → (S ⋆ (idEquiv X)) ≡ idEquiv (S X)
⋆-idEquiv S X = (S ⋆ (idEquiv X))  ≡⟨ cong (λ p → pathToEquiv (cong S p)) uaIdEquiv  ⟩
                pathToEquiv refl   ≡⟨ pathToEquivRefl ⟩
                idEquiv (S X)      ∎

⋆-char : (S : Type ℓ → Type ℓ') (X Y : Type ℓ) (f : X ≃ Y) → ua (S ⋆ f) ≡ cong S (ua f)
⋆-char S X Y f = ua-lemma-2 (S X) (S Y) (cong S (ua f))

PathP-⋆-lemma : (S : Type ℓ → Type ℓ') (A B : Σ[ X ∈ (Type ℓ) ] (S X)) (f : (A .fst) ≃ (B .fst))
    → (PathP (λ i →  ua (S ⋆ f) i) (A .snd) (B .snd)) ≡ (PathP (λ i → S ((ua f) i)) (A .snd) (B .snd))
PathP-⋆-lemma S A B f i = PathP (λ j → (⋆-char S (A .fst) (B .fst) f) i j) (A .snd) (B .snd)
     

-- Our new definition of standard notion of structure that appears to be rather strong.
-- Maybe find something later
SNS' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS'  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → ((equivFun (S ⋆ f)) (A .snd) ≡ (B .snd)) ≃ (ι A B f)


-- A quick sanity-check that our definition is interchangeable with Escardó's:
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


-- Our version of ρ although we won't need it
ρ' : {S : Type ℓ → Type ℓ'}
    → {ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''}
    → (θ : SNS' S ι)
    → (A : Σ[ X ∈ (Type ℓ) ] (S X)) → (ι A A (idEquiv (A .fst)))
ρ' {S = S} {ι = ι} θ A = equivFun (θ A A (idEquiv (A .fst)))
                        (subst (λ f → (f .fst) (A .snd) ≡ (A .snd)) (sym (⋆-idEquiv S (A .fst))) refl)


-- We want to show that
--        (SNS' S ι) → (A ≃[ ι ] B) ≃ (A ≡ B)
-- Using the cubical machinery we might be able to construct an isomorphism directly.
-- Our version of Id→homEq not using J and ρ':
pis :  (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → (θ : SNS' S ι)
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (A ≡ B) → (A ≃[ ι ] B)
pis S ι θ A B r = f , equivFun (θ A B f) (λ i → unglue (i ∨ ~ i) (q⋆⋆ i))
   where
    p = λ i → r i .fst
    f = pathToEquiv p
    
    q : PathP (λ i → S (p i)) (A .snd) (B .snd)
    q = λ i → r i .snd
    
    q⋆ : PathP (λ i → S (ua f i)) (A .snd) (B .snd)
    q⋆ = subst (λ p →  PathP (λ i → S (p i)) (A .snd) (B .snd))
               (sym (ua-lemma-2 (A .fst) (B .fst) p)) q
               
    q⋆⋆ : PathP (λ i → ua (S ⋆ f) i) (A .snd) (B .snd)
    q⋆⋆ = transport (λ i → PathP-⋆-lemma S A B f (~ i)) q⋆


-- Now we can also explicitly construct the inverse:
sip :  (S : Type ℓ → Type ℓ')
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


-- hopefully we can prove that pis and sip are mutually inverse
sip∘pis-id :  (S : Type ℓ → Type ℓ')
            → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
            → (θ : SNS' S ι)
            → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
            → (r : A ≡ B)
            → sip S ι θ A B (pis S ι θ A B r) ≡ r
sip∘pis-id S ι θ A B r i j = ua-lemma-2 (A .fst) (B .fst) (λ i → (r i) .fst) i j , {!!}

-- pis∘sip-id :  (S : Type ℓ → Type ℓ')
--             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
--             → (θ : SNS' S ι)
--             → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
--             → (r : A ≃[ ι ] B)
--             → pis S ι θ A B (sip S ι θ A B r) ≡ r
-- pis∘sip-id S ι θ A B (f , φ) = {!!}


-- Now, we want to add axioms (i.e. propositions) to our Structure S
-- we use a lemma due to Zesen Qian, which can be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83
add-to-structure : (S : Type ℓ → Type ℓ')
                   (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                  → Type ℓ → Type (ℓ-max ℓ' ℓ''')
add-to-structure S axioms X = Σ[ s ∈ S X ] (axioms X s)


add-to-iso : (S : Type ℓ → Type ℓ')
             (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
             (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
            → (A B : Σ[ X ∈ (Type ℓ) ] (add-to-structure S axioms X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''
add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

add-⋆-lemma : (S : Type ℓ → Type ℓ')
              (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
              (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
              {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
              (f : X ≃ Y) → (equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b)) ≃ (equivFun (S ⋆ f) s ≡ t)
add-⋆-lemma S axioms axioms-are-Props {Y = Y} {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
      where
       φ : (equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b)) → (equivFun (S ⋆ f) s ≡ t)
       φ r i = (r i) .fst
       
       ψ : (equivFun (S ⋆ f) s ≡ t) → (equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b))
       ψ p i = p i , isProp-PathP-I (λ j → axioms-are-Props Y (p j)) (equivFun ((add-to-structure S axioms) ⋆ f) (s , a) .snd) b i
       
       η : section φ ψ
       η p = refl
       
       ε : retract φ ψ
       ε r i j = r j .fst , isProp→isSet-PathP (λ k → axioms-are-Props Y (r k .fst)) _ _
                  (λ k → isProp-PathP-I (λ j → axioms-are-Props Y (r j .fst)) (equivFun ((add-to-structure S axioms) ⋆ f) (s , a) .snd) b k)
                  (λ k → (r k) .snd) i j
 

add-axioms-SNS' : (S : Type ℓ → Type ℓ')
                  (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
                  (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                  (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
                  (θ : SNS' S ι) → SNS' (add-to-structure S axioms) (add-to-iso S ι axioms)

add-axioms-SNS' S ι axioms axioms-are-Props θ (X , (s , a)) (Y , (t , b)) f =
               equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b)    ≃⟨ add-⋆-lemma S axioms axioms-are-Props f ⟩
               equivFun (S ⋆ f) s ≡ t                                          ≃⟨ θ (X , s) (Y , t) f ⟩
               (add-to-iso S ι axioms) (X , (s , a)) (Y , (t , b)) f           ■
 

-- module _(S : Type ℓ → Type ℓ')
--         (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
--         (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
--         (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
--         (θ : SNS' S ι)                                                            where

--  S' : Type ℓ → Type (ℓ-max ℓ' ℓ''')
--  S' X = Σ[ s ∈ S X ] (axioms X s)
 
--  ι' : (A B : Σ[ X ∈ (Type ℓ) ] (S' X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''
--  ι' (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

--  axiom-⋆-lemma : {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
--                 (f : X ≃ Y) → (equivFun (S' ⋆ f) (s , a) ≡ (t , b)) ≃ (equivFun (S ⋆ f) s ≡ t)
--  axiom-⋆-lemma {Y = Y} {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
--       where
--        φ : (equivFun (S' ⋆ f) (s , a) ≡ (t , b)) → (equivFun (S ⋆ f) s ≡ t)
--        φ r i = (r i) .fst
       
--        ψ : (equivFun (S ⋆ f) s ≡ t) → (equivFun (S' ⋆ f) (s , a) ≡ (t , b))
--        ψ p i = p i , isProp-PathP-I (λ j → axioms-are-Props Y (p j)) (equivFun (S' ⋆ f) (s , a) .snd) b i
       
--        η : section φ ψ
--        η p = refl
       
--        ε : retract φ ψ
--        ε r i j = r j .fst , isProp→isSet-PathP (λ k → axioms-are-Props Y (r k .fst)) _ _
--                            (λ k → isProp-PathP-I (λ j → axioms-are-Props Y (r j .fst)) (equivFun (S' ⋆ f) (s , a) .snd) b k)
--                            (λ k → (r k) .snd) i j
       
 
--  θ' : SNS' S' ι'
--  θ' (X , (s , a)) (Y , (t , b)) f = equivFun (S' ⋆ f) (s , a) ≡ (t , b) ≃⟨ axiom-⋆-lemma f ⟩
--                                     equivFun (S ⋆ f) s ≡ t              ≃⟨ θ (X , s) (Y , t) f ⟩
--                                     ι (X , s) (Y , t) f                 ≃⟨ idEquiv _ ⟩
--                                     ι' (X , (s , a)) (Y , (t , b)) f    ■
 

-- Now, we want to join two structures
technical-×-lemma : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
                   → (A ≃ C) → (B ≃ D) → (A × B) ≃ (C × D)
technical-×-lemma {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
 where
  φ : (A × B) → (C × D)
  φ (a , b) = equivFun f a , equivFun g b
  
  ψ : (C × D) → (A × B)
  ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

  η : section φ ψ
  η (c , d) i = retEq f c i , retEq g d i
  
  ε : retract φ ψ
  ε (a , b) i = secEq f a i , secEq g b i


join-structure : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
                → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
join-structure S₁ S₂ X = (S₁ X) × (S₂ X)


join-iso : {S₁ : Type ℓ₁ → Type ℓ₂}
           (ι₁ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₁ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄}
           (ι₂ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₂ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₅)
          → (A B : Σ[ X ∈ (Type ℓ₁) ] (join-structure S₁ S₂ X)) → ((A .fst) ≃ (B .fst)) → Type (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)


join-⋆-lemma : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
               {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (f : X ≃ Y)
              → (equivFun ((join-structure S₁ S₂) ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)) ≃ (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
join-⋆-lemma S₁ S₂ {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} f = isoToEquiv (iso φ ψ η ε)
   where
    φ : (equivFun ((join-structure S₁ S₂) ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)) → (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
    φ p = (λ i → (p i) .fst) , (λ i → (p i) .snd)
    
    ψ : (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂) → (equivFun ((join-structure S₁ S₂) ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂))
    ψ (p , q) i = (p i) , (q i)
    
    η : section φ ψ
    η (p , q) = refl
    
    ε : retract φ ψ
    ε p = refl

join-SNS' : (S₁ : Type ℓ₁ → Type ℓ₂)
            (ι₁ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₁ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₃)
            (θ₁ : SNS' S₁ ι₁)
            (S₂ : Type ℓ₁ → Type ℓ₄)
            (ι₂ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₂ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₅)
            (θ₂ : SNS' S₂ ι₂)
           → SNS' (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS' S₁ ι₁ θ₁ S₂ ι₂ θ₂ (X , s₁ , s₂) (Y , t₁ , t₂) f =
 
  equivFun ((join-structure S₁ S₂) ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂) ≃⟨ join-⋆-lemma S₁ S₂ f ⟩
  (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)   ≃⟨ technical-×-lemma (θ₁ (X , s₁) (Y , t₁) f) (θ₂ (X , s₂) (Y , t₂) f)  ⟩
  (join-iso ι₁ ι₂) (X , s₁ , s₂) (Y , t₁ , t₂) f              ■

-- module _(S₁ : Type ℓ₁ → Type ℓ₂)
--         (ι₁ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₁ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₃)
--         (θ₁ : SNS' S₁ ι₁)
--         (S₂ : Type ℓ₁ → Type ℓ₄)
--         (ι₂ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₂ X)) → ((A .fst) ≃ (B .fst)) → Type ℓ₅)
--         (θ₂ : SNS' S₂ ι₂)                                                            where

--  S : Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
--  S X = (S₁ X) × (S₂ X)
 
--  ι : (A B : Σ[ X ∈ (Type ℓ₁) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type (ℓ-max ℓ₃ ℓ₅)
--  ι (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)

--  ⋆-to-×-lemma : {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (f : X ≃ Y)
--                → (equivFun (S ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)) ≃ (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
--  ⋆-to-×-lemma {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} f = isoToEquiv (iso φ ψ η ε)
--    where
--     φ : (equivFun (S ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)) → (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
--     φ p = (λ i → (p i) .fst) , (λ i → (p i) .snd)
    
--     ψ : (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂) → (equivFun (S ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂))
--     ψ (p , q) i = (p i) , (q i)
    
--     η : section φ ψ
--     η (p , q) = refl
    
--     ε : retract φ ψ
--     ε p = refl
--  --  direct proof ? (λ x → φ x) , record { equiv-proof = λ y → (ψ y , refl) , {!!} }

--  θ : SNS' S ι
--  θ (X , s₁ , s₂) (Y , t₁ , t₂) f =
 
--   equivFun (S ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)                      ≃⟨ ⋆-to-×-lemma f ⟩
--   (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)   ≃⟨ technical-×-lemma (θ₁ (X , s₁) (Y , t₁) f) (θ₂ (X , s₂) (Y , t₂) f)  ⟩
--   (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)         ≃⟨ idEquiv _ ⟩
--   ι (X , s₁ , s₂) (Y , t₁ , t₂) f                             ■
 


-- Priorities:
-- Monoids, Groups
-- sip and pis are inverse
-- don't forget about queues


-- Pointed types with SNS'
pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

Pointed-Type : Type (ℓ-suc ℓ)
Pointed-Type {ℓ = ℓ} = Σ (Type ℓ) pointed-structure

pointed-iso : (A B : Pointed-Type) → (A .fst) ≃ (B .fst) → Type ℓ
pointed-iso A B f = (equivFun f) (A .snd) ≡ (B .snd)

pointed-is-SNS' : SNS' {ℓ = ℓ} pointed-structure pointed-iso
pointed-is-SNS' A B f = transportEquiv (λ i → transportRefl (equivFun f (A .snd)) i ≡ B .snd)


-- ∞-Magmas with SNS'
-- need function extensionality for binary functions
funExtBin : {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y}
           → ((x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
funExtBin p i x y = p x y i
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y} where
  private
    appl : f ≡ g → ∀ x y → f x y ≡ g x y
    appl eq x y i = eq i x y

    fib : (p : f ≡ g) → fiber funExtBin p
    fib p = (appl p , refl)

    funExtBin-fiber-isContr
      : (p : f ≡ g)
      → (fi : fiber funExtBin p)
      → fib p ≡ fi
    funExtBin-fiber-isContr p (h , eq) i = (appl (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExtBin-isEquiv : isEquiv funExtBin
  equiv-proof funExtBin-isEquiv p = (fib p , funExtBin-fiber-isContr p)

  funExtBinEquiv : (∀ x y → f x y ≡ g x y) ≃ (f ≡ g)
  funExtBinEquiv = (funExtBin , funExtBin-isEquiv)

-- ∞-Magmas
∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ = ℓ} = Σ (Type ℓ) ∞-magma-structure

∞-magma-iso : (A B : ∞-Magma) → (A .fst) ≃ (B .fst) → Type ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f = (x x' : X) → equivFun f (x · x') ≡ (equivFun f x) ∗ (equivFun f x')

-- a more direct proof possible??
∞-magma-is-SNS' : SNS' {ℓ = ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS' (X , _·_) (Y , _∗_) f = SNS→SNS' ∞-magma-structure ∞-magma-iso C (X , _·_) (Y , _∗_) f
 where 
  C : {X : Type ℓ} (_·_ _∗_ : X → X → X) → (_·_ ≡ _∗_) ≃ ((x x' : X) → (x · x') ≡ (x ∗ x'))
  C _·_ _∗_ = invEquiv funExtBinEquiv



-- Now we're getting serious: Monoids
monoid-structure : Type ℓ → Type ℓ
monoid-structure X = X × (X → X → X)

monoid-axioms : (X : Type ℓ) → monoid-structure X → Type ℓ
monoid-axioms X (e , _·_ ) = isSet X
                          × ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z))
                          × ((x : X) → (x · e) ≡ x)
                          × ((x : X) → (e · x) ≡ x)

monoid-iso : (M N : Σ (Type ℓ) monoid-structure) → (M .fst) ≃ (N .fst) → Type ℓ
monoid-iso (M , e , _·_) (N , d , _∗_) f = (equivFun f e ≡ d)
                        × ((x y : M) → equivFun f (x · y) ≡ (equivFun f x) ∗ (equivFun f y))

Raw-Monoid-SNS' : SNS' {ℓ = ℓ} monoid-structure monoid-iso
Raw-Monoid-SNS' = join-SNS' pointed-structure pointed-iso pointed-is-SNS' ∞-magma-structure ∞-magma-iso ∞-magma-is-SNS'

