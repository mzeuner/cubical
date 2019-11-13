{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Equivalences  where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties

private
 variable
  ℓ ℓ' ℓ'' : Level



-- We prove several useful equalities and equivalences between Σ-types all the proofs are taken from
-- Martin Hötzel-Escardó's lecture notes.
-- We begin by introducing some helpful notation.

_≃⟨_⟩_ : (X : Type ℓ) {Y : Type ℓ'} {Z : Type ℓ''} → (X ≃ Y) → (Y ≃ Z) → (X ≃ Z)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (X : Type ℓ) → (X ≃ X)
_■ = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

-- The next result is just a reformulation of pathSigma≡sigmaPath from Sigma.Properties.

Σ-≡-≃ : {X : Type ℓ} {A : X → Type ℓ'}
       → (σ τ : Σ X A) → ((σ ≡ τ) ≃ (Σ[ p ∈ (σ .fst) ≡ (τ .fst) ] (subst A p (σ .snd) ≡ (τ .snd))))
Σ-≡-≃ {A = A} σ τ = pathToEquiv (pathSigma≡sigmaPath σ τ)



-- This cubical proof is much shorter than in HoTT but requires that A, B live in the same universe.
Σ-cong : {X : Type ℓ} {A B : X → Type ℓ'} →
         ((x : X) → (A x ≡ B x)) → (Σ X A ≡ Σ X B)
Σ-cong {X = X} p i = Σ[ x ∈ X ] (p x i)

-- Two lemmas for the more general formulation using equivalences
NatΣ : {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''}
      → ((x : X) → (A x) → (B x)) → (Σ X A) → (Σ X B)
NatΣ τ (x , a) = (x , τ x a)

Σ-to-PathP : {X : Type ℓ} {A : X → Type ℓ'} {x : X} {a b : A x}
          → (a ≡ b) → PathP (λ i → Σ X A) (x , a) (x , b)
Σ-to-PathP {x = x} p i = (x , p i)


Σ-cong-≃ :  {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} →
         ((x : X) → (A x ≃ B x)) → (Σ X A ≃ Σ X B)
Σ-cong-≃ {X = X} {A = A} {B = B} φ = isoToEquiv (iso (NatΣ f) (NatΣ g) NatΣ-ε NatΣ-η)
 where
  f : (x : X) → (A x) → (B x)
  f x = equivFun (φ x)

  g : (x : X) → (B x) → (A x)
  g x = equivFun (invEquiv (φ x))

  η : (x : X) → (a : A x) → (g x) ((f x) a) ≡ a
  η x = retEq (invEquiv (φ x))

  ε : (x : X) → (b : B x) → f x (g x b) ≡ b
  ε x = secEq  (invEquiv (φ x))

  NatΣ-η : (w : Σ X A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a)  = (x , g x (f x a)) ≡⟨ Σ-to-PathP (η x a)  ⟩
                    (x , a)           ∎

  NatΣ-ε : (u : Σ X B) → NatΣ f (NatΣ g u) ≡ u
  NatΣ-ε (x , b) = (x , f x (g x b)) ≡⟨ Σ-to-PathP (ε x b) ⟩
                   (x , b)           ∎



-- The next result is stated a bit awkwardly but is rather straightforward to prove.
Σ-change-of-variable-Iso :  {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                           → (isHAEquiv f) → (Iso (Σ X (A ∘ f)) (Σ Y A))
Σ-change-of-variable-Iso {ℓ = ℓ} {ℓ' = ℓ'} {X = X} {Y = Y} {A = A} f isHAEquivf = iso φ ψ φψ ψφ
  where
   g : Y → X
   g = isHAEquiv.g isHAEquivf
   ε : (x : X) → (g (f x)) ≡ x
   ε = isHAEquiv.sec isHAEquivf
   η : (y : Y) → f (g y) ≡ y
   η = isHAEquiv.ret isHAEquivf
   τ :  (x : X) → cong f (ε x) ≡ η (f x)
   τ = isHAEquiv.com isHAEquivf
   
   φ : (Σ X (A ∘ f)) → (Σ Y A)
   φ (x , a) = (f x , a)

   ψ : (Σ Y A) → (Σ X (A ∘ f))
   ψ (y , a) = (g y , subst A (sym (η y)) a)

   φψ : (z : (Σ Y A)) → φ (ψ z) ≡ z
   φψ (y , a) = sigmaPath→pathSigma (φ (ψ (y , a))) (y , a)
                                    (η y ,  transportTransport⁻ (λ i → A (η y i)) a)
     -- last term proves transp (λ i → A (η y i)) i0 (transp (λ i → A (η y (~ i))) i0 a) ≡ a

   ψφ : (z : (Σ X (A ∘ f))) → ψ (φ z) ≡ z 
   ψφ (x , a) = sigmaPath→pathSigma (ψ (φ (x , a))) (x , a) (ε x , q)
     where
      b : A (f (g (f x)))
      b = (transp (λ i → A (η (f x) (~ i))) i0 a)
    
      q : transp (λ i → A (f (ε x i))) i0 (transp (λ i → A (η (f x) (~ i))) i0 a) ≡ a
      q =  transp (λ i → A (f (ε x i))) i0 b  ≡⟨ S ⟩
           transp (λ i → A (η (f x) i)) i0 b  ≡⟨ transportTransport⁻ (λ i → A (η (f x) i)) a ⟩
           a                                  ∎
       where
        S : (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (η (f x) i)) i0 b)
        S = subst (λ p → (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (p i)) i0 b))
                 (τ x) refl


-- Using the result above we can prove the following quite useful result.
Σ-change-of-variable-≃ : {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                      → (isEquiv f) → ((Σ X (A ∘ f)) ≃ (Σ Y A))
Σ-change-of-variable-≃ f isEquivf =
                      isoToEquiv (Σ-change-of-variable-Iso f (equiv→HAEquiv (f , isEquivf) .snd))




-- Is this done somewhere already?
Σ-assoc-Iso : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Iso (Σ (Σ X A) P) (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))))
Σ-assoc-Iso X A P = iso f g ε η
   where
    f : (Σ (Σ X A) P) → (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
    f ((x , a) , p) = (x , (a , p))
    g : (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))) →  (Σ (Σ X A) P)
    g (x , (a , p)) = ((x , a) , p)
    ε : section f g
    ε n = refl
    η : retract f g
    η m = refl

Σ-assoc-≃ : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Σ (Σ X A) P) ≃ (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
Σ-assoc-≃ X A P = isoToEquiv (Σ-assoc-Iso X A P)

