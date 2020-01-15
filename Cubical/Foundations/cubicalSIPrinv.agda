{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.cubicalSIPtest where

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

-- Attempt to clarify what is going on

lemma1 : (S : Type ℓ → Type ℓ')
         (A B : Σ[ X ∈ (Type ℓ) ] (S X))
         (e : A .fst ≃ B .fst)
       → PathP (λ i → ua (au (cong S (ua e))) i) (A .snd) (B .snd) ≡
         PathP (λ i → S (ua e i)) (A .snd) (B .snd)
lemma1 S A B e i = PathP (λ j → ua-au (cong S (ua e)) i j) (A .snd) (B .snd)

lemma2 : (S : Type ℓ → Type ℓ')
         (A B : Σ[ X ∈ (Type ℓ) ] (S X))
         (e : A .fst ≡ B .fst)
       → PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd) ≡
         PathP (λ i → S (e i)) (A .snd) (B .snd)
lemma2 S A B e i = PathP (λ j → S (ua-au e i j)) (A .snd) (B .snd)



-- write pairs explicitly and everything in one line
sip : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (θ : SNS' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → (A ≃[ ι ] B)
    → Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
sip S ι θ A B (e , p) = ua e , r
-- transport (λ i → lemma1 S A B e i) (λ i → glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) }) ((invEquiv (θ A B e) .fst p) i))
   where
    q : au (cong S (ua e)) .fst (A .snd) ≡ B .snd
    q = invEquiv (θ A B e) .fst p

    q⋆ : PathP (λ i → ua (au (cong S (ua e))) i) (A .snd) (B .snd)
    q⋆ i = glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) }) (q i)

    r : PathP (λ i → S (ua e i)) (A .snd) (B .snd)
    r = transport (λ i → lemma1 S A B e i) q⋆



-- write pairs explicitly and everything in one line
pis : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
    → (Θ : SNS' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → (Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd)))
    → A ≃[ ι ] B
pis S ι Θ A B (e , p) = au e , r
-- Θ A B (au e) .fst λ i →  unglue (i ∨ ~ i) (transport (λ i → lemma1 S A B (au e) (~ i)) (transport (λ i → lemma2 S A B e (~ i)) p) i)
  where
  -- This is what doesn't occur in sip, but I don't see how to modify
  -- the sip so that it is there as well (but in the other direction).
  foo : PathP (λ i → S (ua (au e) i)) (A .snd) (B .snd)
  foo = transport (λ i → lemma2 S A B e (~ i)) p

  q⋆ : PathP (λ i → ua (au (cong S (ua (au e)))) i) (A .snd) (B .snd)
  q⋆ = transport (λ i → lemma1 S A B (au e) (~ i)) foo

  q : au (cong S (ua (au e))) .fst (A .snd) ≡ B .snd
  q i = unglue (i ∨ ~ i) (q⋆ i)

  r : ι A B (au e)
  r = Θ A B (au e) .fst q


sip∘pis-id : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
           → (θ : SNS' S ι)
           → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (r : Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd)))
           → sip S ι θ A B (pis S ι θ A B r) ≡ r
sip∘pis-id S ι θ A B (p , q) =  sip S ι θ A B (pis S ι θ A B (p , q))


                     ≡⟨ refl ⟩ --unfolding the definition

                               ua (au p) ,  transport (λ i → lemma1 S A B (au p) i) (λ i → glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) })
                           ((invEquiv (θ A B (au p)) .fst (θ A B (au p) .fst   --this cancels out first
                           λ i →  unglue (i ∨ ~ i) (transport (λ i → lemma1 S A B (au p) (~ i)) (transport (λ i → lemma2 S A B p (~ i)) q) i))) i))

                     ≡⟨ i ⟩  
                                 
                                ua (au p) ,  transport (λ i → lemma1 S A B (au p) i)
                                            (λ i → glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) }) (unglue (i ∨ ~ i)
                                            (transport (λ i → lemma1 S A B (au p) (~ i)) (transport (λ i → lemma2 S A B p (~ i)) q) i)))

                     ≡⟨ refl ⟩  --glue and unglue cancel judgementally

                                ua (au p) ,  transport (λ i → lemma1 S A B (au p) i) (transport⁻ (λ i → lemma1 S A B (au p) i)
                                            (transport (λ i → lemma2 S A B p (~ i)) q))                                            

                     ≡⟨ ii ⟩

                                ua (au p) , transport (λ i → lemma2 S A B p (~ i)) q

                     ≡⟨ iii ⟩
                                
                                p , transport (λ i → lemma2 S A B p i) (transport (λ i → lemma2 S A B p (~ i)) q)

                     ≡⟨ iv ⟩

                                p , q  ∎

 where
  i = λ j → ua (au p) , transport (λ i → lemma1 S A B (au p) i) (λ i → glue (λ { (i = i0) → (A .snd) ; (i = i1) → (B .snd) }) (secEq (θ A B (au p))
                       (λ k →  unglue (k ∨ ~ k) (transport (λ i → lemma1 S A B (au p) (~ i)) (transport (λ i → lemma2 S A B p (~ i)) q) k)) j i))
  ii = (λ i → ua (au p) , transportTransport⁻ (lemma1 S A B (au p)) (transport (λ i → lemma2 S A B p (~ i)) q) i)
  iii = (λ i → ua-au p i , transp (λ k →  (PathP (λ j → S (ua-au p (i ∧ k) j)) (A .snd) (B .snd))) (~ i) (transport (λ i → lemma2 S A B p (~ i)) q))
  iv = (λ i → p , transportTransport⁻ (lemma2 S A B p) q i)



-- ua-au e i , {!!} -- As the first component is proved using J the best is probably
--                  -- to use J for the second as well. Maybe after some manual simplifications

-- pis∘sip-id : (S : Type ℓ → Type ℓ')
--            → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A .fst) ≃ (B .fst)) → Type ℓ'')
--            → (θ : SNS' S ι)
--            → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
--            → (r : A ≃[ ι ] B)
--            → pis S ι θ A B (sip S ι θ A B r) ≡ r
-- pis∘sip-id S ι θ A B (f , φ) i = au-ua f i , {!!} -- As the first component is proved using EquivJ the best is probably to use EquivJ for the second as well

