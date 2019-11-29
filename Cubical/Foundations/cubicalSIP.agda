{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.cubicalSIP where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma.Equivalences

private
 variable
  ℓ ℓ' ℓ'' ℓ''' : Level
 
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
-- First, we define the "push-forward" of an equivalence:
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
    p = λ i → ((r i) .fst)
    f = pathToEquiv p
    
    q : PathP (λ i → S (p i)) (A .snd) (B .snd)
    q = λ i → ((r i) .snd)
    
    q⋆ : PathP (λ i → S (ua f i)) (A .snd) (B .snd)
    q⋆ = subst (λ p →  PathP (λ i → S (p i)) (A .snd) (B .snd))
               (sym (ua-lemma-2 (A .fst) (B .fst) p)) q
               
    q⋆⋆ : PathP (λ i → ua (S ⋆ f) i) (A .snd) (B .snd)
    q⋆⋆ =  transport (λ i → PathP-⋆-lemma S A B f (~ i)) q⋆


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
-- sip∘pis-id :  (S : Type ℓ → Type ℓ')
--             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
--             → (θ : SNS' S ι)
--             → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
--             → (r : A ≡ B)
--             → sip S ι θ A B (pis S ι θ A B r) ≡ r
-- sip∘pis-id S ι θ A B r = {!!}

-- pis∘sip-id :  (S : Type ℓ → Type ℓ')
--             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
--             → (θ : SNS' S ι)
--             → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
--             → (r : A ≃[ ι ] B)
--             → pis S ι θ A B (sip S ι θ A B r) ≡ r
-- pis∘sip-id S ι θ A B (f , φ) = {!!}


-- Now, we want to add axioms (i.e. propositions) to our Structure S
-- we use the following lemma due to Andrea Vezzosi:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83
axiom-lemma : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i)) → {b0 : B i0} {b1 : B i1}
             → PathP (λ i → B i) b0 b1
axiom-lemma hB = toPathP (hB _ _ _)

-- axiom-lemma-isProp : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i)) → {b0 : B i0} {b1 : B i1}
--              → isProp (PathP (λ i → B i) b0 b1)
-- axiom-lemma-isProp hB p q i j = {!(hB j) (p j) (q j) i!}

module _(S : Type ℓ → Type ℓ')
        (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
        (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
        (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
        (θ : SNS' S ι)                                                            where

 S' : Type ℓ → Type (ℓ-max ℓ' ℓ''')
 S' X = Σ[ s ∈ S X ] (axioms X s)
 
 ι' : (A B : Σ[ X ∈ (Type ℓ) ] (S' X)) → ((A .fst) ≃ (B .fst)) → Type ℓ''
 ι' (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

 axiom-⋆-lemma : {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
                (f : X ≃ Y) → (equivFun (S' ⋆ f) (s , a) ≡ (t , b)) ≃ (equivFun (S ⋆ f) s ≡ t)
 axiom-⋆-lemma {Y = Y} {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
      where
       φ : (equivFun (S' ⋆ f) (s , a) ≡ (t , b)) → (equivFun (S ⋆ f) s ≡ t)
       φ r i = (r i) .fst
       
       ψ : (equivFun (S ⋆ f) s ≡ t) → (equivFun (S' ⋆ f) (s , a) ≡ (t , b))
       ψ p i = p i , axiom-lemma (λ j → axioms-are-Props Y (p j)) {b0 = equivFun (S' ⋆ f) (s , a) .snd} {b1 = b} i
       
       η : section φ ψ
       η p = refl
       
       ε : retract φ ψ
       ε r =  λ i j → (r j) .fst , {!!}
       -- λ i j → (r j) .fst , {!!}
       
 
 θ' : SNS' S' ι'
 θ' (X , (s , a)) (Y , (t , b)) f = equivFun (S' ⋆ f) (s , a) ≡ (t , b) ≃⟨ axiom-⋆-lemma f ⟩
                                    equivFun (S ⋆ f) s ≡ t              ≃⟨ θ (X , s) (Y , t) f ⟩
                                 -- ι (X , s) (Y , t) f                 ≃⟨ idEquiv _ ⟩
                                    ι' (X , (s , a)) (Y , (t , b)) f    ■
 

