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

SNS'≡SNS'' : (S : Type ℓ → Type ℓ')
            → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
            → SNS' S ι ≡ SNS'' S ι
SNS'≡SNS'' S ι = refl

SNS''' : (S : Type ℓ → Type ℓ')
     → ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS'''  {ℓ = ℓ} S ι = (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (f : (A .fst) ≃ (B .fst))
                  → (PathP (λ i → S (ua f i)) (A .snd) (B .snd)) ≃ (ι A B f)

SNS''→SNS''' : (S : Type ℓ → Type ℓ')
             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
             → SNS'' S ι
             → SNS''' S ι
SNS''→SNS''' S ι h A B f =  PathP (λ i → S (ua f i)) (A .snd) (B .snd)
                         ≃⟨ PathP≃Path (λ i → S (ua f i)) (A .snd) (B .snd) ⟩
                            h A B f

SNS'''→SNS'' : (S : Type ℓ → Type ℓ')
             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
             → SNS''' S ι
             → SNS'' S ι
SNS'''→SNS'' S ι h A B f =  transport (λ i → S (ua f i)) (A .snd) ≡ (B .snd)
                         ≃⟨ invEquiv (PathP≃Path (λ i → S (ua f i)) (A .snd) (B .snd)) ⟩
                            h A B f


-- SIP expressed using Path
sipPath : (S : Type ℓ → Type ℓ')
        → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
        → (θ : SNS''' S ι)
        → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
        → A ≃[ ι ] B
        → A ≡ B
sipPath S ι θ A B (e , p) i = ua e i , invEq (θ A B e) p i

pisPath : (S : Type ℓ → Type ℓ')
        → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
        → (θ : SNS''' S ι)
        → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
        → A ≡ B
        → A ≃[ ι ] B
pisPath S ι θ A B p = au e , θ A B (au e) .fst q
  where
  e : A .fst ≡ B .fst
  e = λ i → p i .fst

  r : PathP (λ i → S (e i)) (A .snd) (B .snd)
  r i = p i .snd

  eq : PathP (λ i → S (e i)) (A .snd) (B .snd) ≡ PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  eq i = PathP (λ j → S (ua-au e (~ i) j)) (A .snd) (B .snd)

  q : PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  q = transport eq r

lemma2 : (S : Type ℓ → Type ℓ')
         (A B : Σ[ X ∈ (Type ℓ) ] (S X))
         (e : A .fst ≡ B .fst)
       → PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd) ≡
         PathP (λ i → S (e i)) (A .snd) (B .snd)
lemma2 S A B e i = PathP (λ j → S (ua-au e i j)) (A .snd) (B .snd)

-- SIP expressed using Σ-type instead (easier to work with?)
sip : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → A ≃[ ι ] B
    → Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
sip S ι θ A B (e , p) = ua e , invEq (θ A B e) p

pis : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
    → A ≃[ ι ] B
pis S ι θ A B (e , r) = au e , θ A B (au e) .fst q
  where
  q : PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  q = transport (λ i → lemma2 S A B e (~ i)) r

-- These should now be more feasible:

sip∘pis-id : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
           → (θ : SNS''' S ι)
           → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (r : Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd)))
           → sip S ι θ A B (pis S ι θ A B r) ≡ r
sip∘pis-id S ι θ A B (p , q) =
    sip S ι θ A B (pis S ι θ A B (p , q))
  ≡⟨ refl ⟩
    ua (au p) , invEq (θ A B (au p)) (θ A B (au p) .fst (transport (λ i → lemma2 S A B p (~ i)) q))
  ≡⟨ (λ i → ua (au p) , secEq (θ A B (au p)) (transport (λ i → lemma2 S A B p (~ i)) q) i) ⟩
    ua (au p) , transport (λ i → lemma2 S A B p (~ i)) q
  ≡⟨ (λ i → ua-au p i , transp (λ k →  (PathP (λ j → S (ua-au p (i ∧ k) j)) (A .snd) (B .snd))) (~ i) (transport (λ i → lemma2 S A B p (~ i)) q)) ⟩
    p , transport (λ i → lemma2 S A B p i) (transport (λ i → lemma2 S A B p (~ i)) q)
  ≡⟨ (λ i → p , transportTransport⁻ (lemma2 S A B p) q i) ⟩
    p , q ∎

pis∘sip-id : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
           → (θ : SNS''' S ι)
           → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (r : A ≃[ ι ] B)
           → pis S ι θ A B (sip S ι θ A B r) ≡ r
pis∘sip-id S ι θ A B (e , p) =
    pis S ι θ A B (sip S ι θ A B (e , p))
  ≡⟨ refl ⟩
    au (ua e) , θ A B (au (ua e)) .fst (transport (λ i → lemma2 S A B (ua e) (~ i)) (invEq (θ A B e) p))
  ≡⟨ (λ i → au-ua e i , θ A B (au-ua e i) .fst (transp (λ k → PathP (λ j → S {!!}) (A .snd) (B .snd)) (~ i) (transport (λ i → lemma2 S A B (ua e) (~ i)) (invEq (θ A B e) p)))) ⟩
    e , θ A B e .fst (transport (λ i → lemma2 S A B (ua e) i) (transport (λ i → lemma2 S A B (ua e) (~ i)) (invEq (θ A B e) p)))
  ≡⟨ (λ i → e , θ A B e .fst (transportTransport⁻ (lemma2 S A B (ua e)) (invEq (θ A B e) p) i)) ⟩
    e , θ A B e .fst (invEq (θ A B e) p)
  ≡⟨ (λ i → e , (retEq (θ A B e) p i)) ⟩
    e , p ∎
