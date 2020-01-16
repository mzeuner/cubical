{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.cubicalSIP2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma.Equivalences
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)


private
 variable
  ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

-- Some shorter names for now:
au = pathToEquiv

ua-au : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → ua (au p) ≡ p
ua-au {A = A} {B = B} p = J (λ b p → ua (au p) ≡ p)
                            (cong ua (pathToEquivRefl {A = A}) ∙ uaIdEquiv) p

au-ua : {A B : Type ℓ} (e : A ≃ B) → au (ua e) ≡ e
au-ua {A = A} {B = B} e =
  EquivJ (λ b a f → au (ua f) ≡ f)
         (λ x → subst (λ r → au r ≡ idEquiv x) (sym uaIdEquiv) pathToEquivRefl)
         B A e

-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : {S : Type ℓ → Type ℓ'} → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
                           → (Σ[ X ∈ (Type ℓ) ] (S X))
                           → (Type (ℓ-max ℓ ℓ''))
A ≃[ ι ] B = Σ[ f ∈ ((A .fst) ≃ (B. fst)) ] (ι A B f)

-- original (slightly modified) definition of SNS:
SNS : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS  {ℓ = ℓ} S ι = ∀ {X : (Type ℓ)} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))

SNS' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS'  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → ((equivFun (au (cong S (ua f)))) (A .snd) ≡ (B .snd)) ≃ (ι A B f)

SNS'' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS''  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → (transport (λ i → S (ua f i)) (A .snd) ≡ (B .snd)) ≃ (ι A B f)

sanitycheck : (S : Type ℓ → Type ℓ')
            → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
            → SNS' S ι ≡ SNS'' S ι
sanitycheck S ι = refl

SNS''' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS'''  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → (PathP (λ i → S (ua f i)) (A .snd) (B .snd)) ≃ (ι A B f)


lem1 : (S : Type ℓ → Type ℓ')
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
     → PathP (λ i → S (ua f i)) (A .snd) (B .snd) 
     ≃ (transport (λ i → S (ua f i)) (A .snd) ≡ (B .snd))
lem1 S A B f = PathP≃Path (λ i → S (ua f i)) (A .snd) (B .snd)

foo : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → SNS'' S ι
    → SNS''' S ι
foo S ι h A B f = PathP (λ i → S (ua f i)) (A .snd) (B .snd) ≃⟨ lem1 S A B f ⟩ h A B f


sip : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → (A ≃[ ι ] B)
    → A ≡ B
sip S ι θ A B (e , p) i = (ua e i) , invEquiv (θ A B e) .fst p i

pis : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → A ≡ B
    → A ≃[ ι ] B
pis S ι θ A B p = au e , θ A B (au e) .fst q
  where
  e : A .fst ≡ B .fst
  e = λ i → p i .fst

  r : PathP (λ i → S (e i)) (A .snd) (B .snd)
  r i = p i .snd

  eq : PathP (λ i → S (e i)) (A .snd) (B .snd) ≡ PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  eq i = PathP (λ j → S (ua-au e (~ i) j)) (A .snd) (B .snd)

  q : PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  q = transport eq r

-- These should now be more feasible:

sip∘pis-id : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
           → (θ : SNS''' S ι)
           → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (r : A ≡ B)
           → sip S ι θ A B (pis S ι θ A B r) ≡ r
sip∘pis-id S ι θ A B r = {!!}

-- This is the one I really need. It says that A ≃[ ι ] B is a retract
-- of A ≡ B, which should be sufficient to prove that sip is an
-- equivalence. But if one can prove both directly then that's the
-- best.
pis∘sip-id : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
           → (θ : SNS''' S ι)
           → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (r : A ≃[ ι ] B)
           → pis S ι θ A B (sip S ι θ A B r) ≡ r
pis∘sip-id S ι θ A B (f , φ) i = au-ua f i , {!!}

