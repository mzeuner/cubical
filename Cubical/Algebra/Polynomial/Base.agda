{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Algebra.Polynomial.Base where
{-
  This file contains
    ∙ the definition of the 'polynomial' R-algebra structure on lists
    ∙ a list-based HIT
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (const)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring        using ()
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Algebra     hiding (⟨_⟩a)

open import Cubical.Data.List.Base as L
open import Cubical.Data.List.Properties
open import Cubical.HITs.SetTruncation as ST

private
  variable
    ℓ ℓ′ : Level

module ListsAsQuasiR-Alg (R' : CommRing {ℓ}) where
 private
  R = fst R'
 open CommRingStr (snd R')


 _+ₗ_ : List R → List R → List R
 [] +ₗ ys = ys
 xs +ₗ [] = xs
 (x ∷ xs) +ₗ (y ∷ ys) = (x + y) ∷ (xs +ₗ ys)

 _·ₗ_ : List R → List R → List R
 [] ·ₗ ys = []
 xs ·ₗ [] = []
 (x ∷ xs) ·ₗ (y ∷ ys) = (x · y) ∷ (((x ∷ xs) ·ₗ ys) +ₗ (xs ·ₗ (y ∷ ys)))

 -ₗ_ : List R → List R
 -ₗ_ = L.map (-_)

 _⋆ₗ_ : R → List R → List R
 (_⋆ₗ_) r = L.map (r ·_)

 0ₗ : List R
 0ₗ = []

 1ₗ : List R
 1ₗ = [ 1r ]

 +ₗ-assoc : (xs ys zs : List R) → xs +ₗ (ys +ₗ zs) ≡ (xs +ₗ ys) +ₗ zs
 +ₗ-assoc [] ys zs = refl
 +ₗ-assoc (x ∷ xs) [] zs = refl
 +ₗ-assoc (x ∷ xs) (y ∷ ys) [] = refl
 +ₗ-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ (_∷_) (+-assoc _ _ _) (+ₗ-assoc xs ys zs)

 -- ·ₗ-assoc : (xs ys zs : List R) → xs ·ₗ (ys ·ₗ zs) ≡ (xs ·ₗ ys) ·ₗ zs
 -- ·ₗ-assoc [] ys zs = refl
 -- ·ₗ-assoc (x ∷ xs) [] zs = refl
 -- ·ₗ-assoc (x ∷ xs) (y ∷ ys) [] = refl
 -- ·ₗ-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ (_∷_) (·-assoc _ _ _) {!!}

module polyHIT (R' : CommRing {ℓ}) where
 private
  R = fst R'
 open CommRingStr (snd R')

 data ListPoly : Type ℓ where
  l→p : List R → ListPoly
  del : ∀ (xs : List R) → l→p (xs ++ [ 0r ]) ≡ l→p xs
  trunc : isSet ListPoly

 module Elim {ℓ'} {B : ListPoly → Type ℓ'}
   (l→p* : (xs : List R) → B (l→p xs))
   (del* : (xs : List R) → PathP (λ i → B (del xs i)) (l→p* (xs ++ [ 0r ])) (l→p* xs))
   (trunc* : (p : ListPoly) → isSet (B p)) where

  f : (p : ListPoly) → B p
  f (l→p xs) = l→p* xs
  f (del xs i) = del* xs i
  f (trunc p q α β i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f p) (f q) (cong f α) (cong f β) (trunc p q α β) i j

 module ElimProp {ℓ'} {B : ListPoly → Type ℓ'} (BProp : {p : ListPoly} → isProp (B p))
                 (l→p* : (xs : List R) → B (l→p xs)) where

  f : (p : ListPoly) → B p
  f = Elim.f l→p* (λ xs → toPathP (BProp (transp (λ i → B (del xs i)) i0 (l→p* (xs ++ [ 0r ]))) (l→p* xs)))
                  (λ _ → isProp→isSet BProp)

 module Rec {ℓ'} {B : Type ℓ'} (Bset : isSet B)
   (l→p* : List R → B)
   (del* : (xs : List R) → l→p* (xs ++ [ 0r ]) ≡ l→p* xs) where

   f : ListPoly → B
   f = Elim.f l→p* del* (λ _ → Bset)

 module Rec2 {ℓ'} {B : Type ℓ'} (Bset : isSet B)
             (l→p*2 : List R → List R → B)
             (del*2r : (xs ys : List R) → l→p*2 xs (ys ++ [ 0r ]) ≡ l→p*2 xs ys)
             (del*2l : (xs ys : List R) → l→p*2 (xs ++ [ 0r ]) ys ≡ l→p*2 xs ys) where

   f : ListPoly → ListPoly → B
   f = Rec.f (isSetΠ (λ _ → Bset)) g λ _ → funExt (ElimProp.f (Bset _ _) (del*2l _))
    where
    g : List R → ListPoly → B
    g xs = Rec.f Bset (λ ys → l→p*2 xs ys) (del*2r _)


 open ListsAsQuasiR-Alg R'
 -- open Theory (CommRing→Ring R')
 -- open CommTheory R'
 -- l→p-∷-lemma : (x : R) (xs ys : List R) → l→p xs ≡ l→p ys → l→p (x ∷ xs) ≡ l→p (x ∷ ys)
 -- l→p-∷-lemma x xs ys p = {!!}


 -- _+ₚ_ : ListPoly → ListPoly → ListPoly
 -- _+ₚ_ = Rec2.f trunc (λ xs ys → l→p (xs +ₗ ys)) cohr {!!}
 --  where
 --  cohr : (xs ys : List R) → l→p (xs +ₗ (ys ++ [ 0r ])) ≡ l→p (xs +ₗ ys)
 --  cohr [] ys = del ys
 --  cohr (x ∷ xs) [] = cong₂ (λ a as → l→p (a ∷ as)) (+-rid _)  {!!}
 --  cohr (x ∷ xs) (x₁ ∷ ys) = l→p-∷-lemma _ _ _ (cohr xs ys)

module polyHIT2 (R' : CommRing {ℓ}) where
 private
  R = fst R'
 open CommRingStr (snd R')

 data ListPoly : Type ℓ where
  0p : ListPoly
  _∷ₚ_ : R → ListPoly → ListPoly
  del : 0r ∷ₚ 0p ≡ 0p
  trunc : isSet ListPoly

{-
 const : R → ListPoly
 _+X*_ : R → ListPoly → ListPoly
 del : (r : R) → r +X* (const 0r) ≡ const r
 trunc ...
-}

 module Elim {ℓ'} {B : ListPoly → Type ℓ'}
   (0p* : B 0p) (_∷ₚ*_ : (r : R) {p : ListPoly} (b : B p) → B (r ∷ₚ p))
   (del* : PathP (λ i → B (del i)) (0r ∷ₚ* 0p*) 0p*)
   (trunc* : (p : ListPoly) → isSet (B p)) where

   f : (p : ListPoly) → B p
   f 0p = 0p*
   f (x ∷ₚ p) = x ∷ₚ* (f p)
   f (del i) = del* i
   f (trunc p q α β i j) =
     isOfHLevel→isOfHLevelDep 2 trunc*  (f p) (f q) (cong f α) (cong f β) (trunc p q α β) i j

 module ElimProp {ℓ'} {B : ListPoly → Type ℓ'} (BProp : {p : ListPoly} → isProp (B p))
   (0p* : B 0p) (_∷ₚ*_ : (r : R) {p : ListPoly} (b : B p) → B (r ∷ₚ p)) where

   f : (p : ListPoly) → B p
   f = Elim.f 0p* _∷ₚ*_ (toPathP (BProp _ _)) λ _ → isProp→isSet BProp

 module Rec {ℓ'} {B : Type ℓ'} (Bset : isSet B)
   (0p* : B) (_∷ₚ*_ : R → B → B)
   (del* : (0r ∷ₚ* 0p*) ≡ 0p*) where

   f : ListPoly → B
   f = Elim.f 0p* (λ x b → x ∷ₚ* b) del* λ _ → Bset

 module Rec2 {ℓ'} {B : Type ℓ'} (Bset : isSet B)
   (0p*2 : B) (∷ₚ*2 : R → B → R → B → B)
    where

 --   f : ListPoly → ListPoly → B
 --   f = Rec.f (isSetΠ (λ _ → Bset)) g λ _ → funExt (ElimProp.f (Bset _ _) (del*2l _))
 --    where
 --    g : List R → ListPoly → B
 --    g xs = Rec.f Bset (λ ys → l→p*2 xs ys) (del*2r _)

 open ListsAsQuasiR-Alg R'
 open Theory (CommRing→Ring R')
 open CommTheory R'

 -ₚ_ : ListPoly → ListPoly
 -ₚ 0p = 0p
 -ₚ (x ∷ₚ xs) = (- x) ∷ₚ (-ₚ xs)
 -ₚ del i = (cong (_∷ₚ 0p) 0-selfinverse ∙ del) i
 -ₚ trunc xs ys p q i j = trunc (-ₚ xs) (-ₚ ys) (cong -ₚ_ p) (cong -ₚ_ q) i j
 -- Rec.f trunc 0p (λ r → (- r) ∷ₚ_) (cong (_∷ₚ 0p) 0-selfinverse ∙ del)

 -- _+ₚ_ : ListPoly → ListPoly → ListPoly
 -- -- _+ₚ_ = Rec.f (isSetΠ (λ _ → trunc)) 0p+ₚ {!!} {!!}
 -- --  where
 -- --  0p+ₚ : ListPoly → ListPoly
 -- --  0p+ₚ = Rec.f trunc 0p _∷ₚ_ del --idFun ListPoly
 -- 0p +ₚ ys = ys
 -- (x ∷ₚ xs) +ₚ 0p = x ∷ₚ xs
 -- (x ∷ₚ xs) +ₚ (y ∷ₚ ys) = (x + y) ∷ₚ (xs +ₚ ys)
 -- (x ∷ₚ xs) +ₚ del i = (+-rid x i) ∷ₚ {!!}
 -- (x ∷ₚ xs) +ₚ trunc ys ys₁ x₁ y i i₁ = {!!}
 -- del i +ₚ 0p = {!!}
 -- del i +ₚ (x ∷ₚ ys) = {!!}
 -- del i +ₚ del i₁ = {!!}
 -- del i +ₚ trunc ys ys₁ x y i₁ i₂ = {!!}
 -- trunc xs xs₁ x y i i₁ +ₚ ys = {!!}

{-
listEval : {A : R-alg} → A → R-AlgHom ListPoly A
freeEval : {A : R-alg} → A ≃ R-AlgHom R[⊤] A

(x : ListPoly) (y : R[⊤]) → {A : R-Alg} → (a : A) → listEval a x ≡ freeEval a y
Question: structured rel. of R-algebras?

=> ListPoly / evalExtensionality ≅[ R-alg ] R[⊤] / evalExt ≅[ R-alg ] R[⊤]
and if discrete R => ListPoly ≅ ListPoly / evalExtensionality

R[X]/⟨rX-1⟩ ≅ R[1/r], r ∈ R
-}
