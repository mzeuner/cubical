
{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.HITs.ZariskiLattice.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
-- open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Algebra.RingSolver.ReflectionSolving

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level

module _ (A' : CommRing {ℓ}) where
 A = fst A'
 open CommRingStr (snd A') renaming (_·_ to _·r_ ; ·-comm to ·r-comm ; ·Assoc to ·rAssoc
                                                 ; ·Lid to ·rLid)
 open Exponentiation A'
 open isMultClosedSubset
 open CommAlgebra ⦃...⦄
 private
  A[1/_] : A → CommAlgebra A'
  A[1/ x ] = AlgLoc.S⁻¹RAsCommAlg A' ([_ⁿ|n≥0] A' x) (powersFormMultClosedSubset _ _)

  A[1/_]ˣ : (x : A) → ℙ (CommAlgebra.Carrier A[1/ x ])
  A[1/ x ]ˣ = (CommAlgebra→CommRing A[1/ x ]) ˣ

 _≼_ : A → A → Type ℓ
 x ≼ y = ∥ Σ[ n ∈ ℕ ] Σ[ z ∈ A ] x ^ n ≡ z ·r y ∥ -- rad(x) ⊆ rad(y)

-- ≼ is a pre-order:

 Refl≼ : isRefl _≼_
 Refl≼ x = PT.∣ 1 , 1r , ·r-comm _ _ ∣

 Trans≼ : isTrans _≼_
 Trans≼ x y z = map2 Trans≼Σ
  where
  Trans≼Σ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y
          → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] y ^ n ≡ a ·r z
          → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r z
  Trans≼Σ (n , a , p) (m , b , q) = n ·ℕ m , (a ^ m ·r b) , path
   where
   path : x ^ (n ·ℕ m) ≡ a ^ m ·r b ·r z
   path = x ^ (n ·ℕ m)    ≡⟨ ^-rdist-·ℕ x n m ⟩
          (x ^ n) ^ m     ≡⟨ cong (_^ m) p ⟩
          (a ·r y) ^ m     ≡⟨ ^-ldist-· a y m ⟩
          a ^ m ·r y ^ m   ≡⟨ cong (a ^ m ·r_) q ⟩
          a ^ m ·r (b ·r z) ≡⟨ ·rAssoc _ _ _ ⟩
          a ^ m ·r b ·r z   ∎


 R : A → A → Type ℓ
 R x y = x ≼ y × y ≼ x -- rad(x) ≡ rad(y)

 RequivRel : isEquivRel R
 RequivRel .reflexive x = Refl≼ x , Refl≼ x
 RequivRel .symmetric _ _ Rxy = (Rxy .snd) , (Rxy .fst)
 RequivRel .transitive _ _ _ Rxy Ryz = Trans≼ _ _ _ (Rxy .fst) (Ryz .fst)
                                     , Trans≼ _ _ _  (Ryz .snd) (Rxy .snd)

 -- The quotient A/R corresponds to the basic opens of the Zariski topology.
 -- Multiplication lifts to the quotient and corresponds to intersection
 -- of basic opens, i.e. we get a meet-semilattice with:
 _∧/_ : A / R → A / R → A / R
 _∧/_ = setQuotSymmBinOp (RequivRel .reflexive) (RequivRel .transitive) _·r_ ·r-comm ·r-lcoh
  where
  ·r-lcoh-≼ : (x y z : A) → x ≼ y → (x ·r z) ≼ (y ·r z)
  ·r-lcoh-≼ x y z = map ·r-lcoh-≼Σ
   where
   path : (x z a y zn : A) →  x ·r z ·r (a ·r y ·r zn) ≡ x ·r zn ·r a ·r (y ·r z)
   path = solve A'

   ·r-lcoh-≼Σ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y
              → Σ[ n ∈ ℕ ] Σ[ a ∈ A ] (x ·r z) ^ n ≡ a ·r (y ·r z)
   ·r-lcoh-≼Σ  (n , a , p) = suc n , (x ·r z ^ n ·r a) , (cong (x ·r z ·r_) (^-ldist-· _ _ _)
                                                       ∙∙ cong (λ v → x ·r z ·r (v ·r z ^ n)) p
                                                       ∙∙ path _ _ _ _ _)

  ·r-lcoh : (x y z : A) → R x y → R (x ·r z) (y ·r z)
  ·r-lcoh x y z Rxy = ·r-lcoh-≼ x y z (Rxy .fst) , ·r-lcoh-≼ y x z (Rxy .snd)

 module ≼ToLoc (x y : A)  where
  private
   instance
    _ = A[1/ x ]
    _ = A[1/ y ]

  lemma : x ≼ y → y ⋆ 1a ∈ A[1/ x ]ˣ
  lemma = PT.rec (A[1/ x ]ˣ (y ⋆ 1a) .snd) lemmaΣ
   where
   path1 : (y z : A) → 1r ·r (y ·r 1r ·r z) ·r 1r ≡ z ·r y
   path1 = solve A'
   path2 : (xn : A) → xn ≡ 1r ·r 1r ·r (1r ·r 1r ·r xn)
   path2 = solve A'

   lemmaΣ : Σ[ n ∈ ℕ ] Σ[ a ∈ A ] x ^ n ≡ a ·r y → y ⋆ 1a ∈ A[1/ x ]ˣ
   lemmaΣ (n , z , p) = [ z , (x ^ n) ,  PT.∣ n , refl ∣ ] -- xⁿ≡zy → y⁻¹ ≡ z/xⁿ
                      , eq/ _ _ ((1r , powersFormMultClosedSubset _ _ .containsOne)
                      , (path1 _ _ ∙∙ sym p ∙∙ path2 _))

 powerIs≽ : (x a : A) → x ∈ ([_ⁿ|n≥0] A' a) → a ≼ x
 powerIs≽ x a = map powerIs≽Σ
  where
  powerIs≽Σ : Σ[ n ∈ ℕ ] (x ≡ a ^ n) → Σ[ n ∈ ℕ ] Σ[ z ∈ A ] (a ^ n ≡ z ·r x)
  powerIs≽Σ (n , p) = n , 1r , sym p ∙ sym (·rLid _)


 𝓞ᴰ : A / R → CommAlgebra A'
 𝓞ᴰ = rec→Gpd.fun isGroupoidCommAlgebra (λ a → A[1/ a ]) RCoh LocPathCoh
    where
    RCoh : ∀ a b → R a b → A[1/ a ] ≡ A[1/ b ]
    RCoh a b (a≼b , b≼a) = fst (isContrS₁⁻¹R≡S₂⁻¹R
             (λ _ x∈[aⁿ|n≥0] → ≼ToLoc.lemma _ _ (Trans≼ _ a _ b≼a (powerIs≽ _ _ x∈[aⁿ|n≥0])))
              λ _ x∈[bⁿ|n≥0] → ≼ToLoc.lemma _ _ (Trans≼ _ b _ a≼b (powerIs≽ _ _ x∈[bⁿ|n≥0])))
     where
     open AlgLocTwoSubsets A' ([_ⁿ|n≥0] A' a) (powersFormMultClosedSubset _ _)
                              ([_ⁿ|n≥0] A' b) (powersFormMultClosedSubset _ _)

    LocPathCoh : ∀ a b → isProp (A[1/ a ] ≡ A[1/ b ])
    LocPathCoh a b = isPropS₁⁻¹R≡S₂⁻¹R
     where
     open AlgLocTwoSubsets A' ([_ⁿ|n≥0] A' a) (powersFormMultClosedSubset _ _)
                              ([_ⁿ|n≥0] A' b) (powersFormMultClosedSubset _ _)





 -- -- might com in handy later
 -- data ZarLat : Type ℓ where
 --   D : A → ZarLat
 --   _∨ₗ_ : ZarLat → ZarLat → ZarLat

 --   -- equivalent to D(x+y) ≤ D(x) ∨ D(y)
 --   +≤∨ : ∀ x y → D (x + y) ≡ D (x · (x + y)) ∨ₗ D (y · (x + y))

 --   ∨ₗ-idem : ∀ d → d ∨ₗ d ≡ d
 --   ∨ₗ-comm : ∀ d e → d ∨ₗ e ≡ e ∨ₗ d
 --   ∨ₗ-assoc : ∀ d e f →  d ∨ₗ (e ∨ₗ f) ≡ (d ∨ₗ e) ∨ₗ f
 --   ∨ₗ-rid : ∀ d → d ∨ₗ D 0r ≡ d
 --   ∨ₗ-rann : ∀ d → d ∨ₗ D 1r ≡ D 1r

 --   trunc : isSet ZarLat

 -- module Elim {ℓ'} {B : ZarLat → Type ℓ'}
 --        (D* : (a : A) → B (D a)) (_∨ₗ*_ : {d e : ZarLat} → B d → B e → B (d ∨ₗ e))
 --        (+≤∨* : (x y : A)
 --              → PathP (λ i → B (+≤∨ x y i)) (D* (x + y)) (D* (x · (x + y)) ∨ₗ* D* (y · (x + y))))
 --        (∨ₗ-idem* : {d : ZarLat} (a : B d)
 --                  → PathP (λ i → B (∨ₗ-idem d i)) (a ∨ₗ* a) a)
 --        (∨ₗ-comm* : {d e : ZarLat} (a : B d) (b : B e)
 --                  → PathP (λ i → B (∨ₗ-comm d e i)) (a ∨ₗ* b) (b ∨ₗ* a))
 --        (∨ₗ-assoc* : {d e f : ZarLat} (a : B d) (b : B e) (c : B f)
 --                   →  PathP (λ i → B (∨ₗ-assoc d e f i)) (a ∨ₗ* (b ∨ₗ* c)) ((a ∨ₗ* b) ∨ₗ* c))
 --        (∨ₗ-rid* : {d : ZarLat} (a : B d)
 --                 → PathP (λ i → B (∨ₗ-rid d i)) (a ∨ₗ* D* 0r) a)
 --        (∨ₗ-rann* : {d : ZarLat} (a : B d)
 --                  → PathP (λ i → B (∨ₗ-rann d i)) (a ∨ₗ* D* 1r) (D* 1r))
 --        (trunc* : (d : ZarLat) → isSet (B d)) where

 --  f : (d : ZarLat) → B d
 --  f (D x) = D* x
 --  f (d ∨ₗ e) = (f d) ∨ₗ* (f e)
 --  f (+≤∨ x y i) = +≤∨* x y i
 --  f (∨ₗ-idem d i) = ∨ₗ-idem* (f d) i
 --  f (∨ₗ-comm d e i) = ∨ₗ-comm* (f d) (f e) i
 --  f (∨ₗ-assoc d e g i) = ∨ₗ-assoc* (f d) (f e) (f g) i
 --  f (∨ₗ-rid d i) = ∨ₗ-rid* (f d) i
 --  f (∨ₗ-rann d i) = ∨ₗ-rann* (f d) i
 --  f (trunc d e p q i j) =
 --           isOfHLevel→isOfHLevelDep 2 trunc*  (f d) (f e) (cong f p) (cong f q) (trunc d e p q) i j


 -- module ElimProp {ℓ'} {B : ZarLat → Type ℓ'} (BProp : {d : ZarLat} → isProp (B d))
 --        (D* : (a : A) → B (D a)) (_∨ₗ*_ : {d e : ZarLat} → B d → B e → B (d ∨ₗ e)) where

 --  f : (d : ZarLat) → B d
 --  f = Elim.f D* _∨ₗ*_
 --      (λ x y → toPathP (BProp (transp (λ i → B (+≤∨ x y i)) i0 (D* (x + y)))
 --                              (D* (x · (x + y)) ∨ₗ* D* (y · (x + y)))))
 --      (λ {d} a → toPathP (BProp (transp (λ i → B (∨ₗ-idem d i)) i0 (a ∨ₗ* a)) a))
 --      (λ {d} {e} a b → toPathP (BProp (transp (λ i → B (∨ₗ-comm d e i)) i0 (a ∨ₗ* b)) (b ∨ₗ* a)))
 --      (λ {d} {e} {g} a b c → toPathP (BProp (transp (λ i → B (∨ₗ-assoc d e g i)) i0
 --                                     (a ∨ₗ* (b ∨ₗ* c))) ((a ∨ₗ* b) ∨ₗ* c)))
 --      (λ {d} a → toPathP (BProp (transp (λ i → B (∨ₗ-rid d i)) i0 (a ∨ₗ* D* 0r)) a))
 --      (λ {d} a → toPathP (BProp (transp (λ i → B (∨ₗ-rann d i)) i0 (a ∨ₗ* D* 1r)) (D* 1r)))
 --      (λ _ → isProp→isSet BProp)


 -- module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
 --        (D* : (a : A) → B) (_∨ₗ*_ : B → B → B)
 --        (+≤∨* : (x y : A) → D* (x + y) ≡ D* (x · (x + y)) ∨ₗ* D* (y · (x + y)))
 --        (∨ₗ-idem* : (a : B) → (a ∨ₗ* a) ≡ a)
 --        (∨ₗ-comm* : (a : B) (b : B) → a ∨ₗ* b ≡ b ∨ₗ* a)
 --        (∨ₗ-assoc* : (a : B) (b : B) (c : B) → a ∨ₗ* (b ∨ₗ* c) ≡ (a ∨ₗ* b) ∨ₗ* c)
 --        (∨ₗ-rid* : (a : B) → a ∨ₗ* D* 0r ≡ a)
 --        (∨ₗ-rann* : (a : B) → a ∨ₗ* D* 1r ≡ D* 1r) where

 --  f : ZarLat → B
 --  f = Elim.f D* _∨ₗ*_ +≤∨* ∨ₗ-idem* ∨ₗ-comm* ∨ₗ-assoc* ∨ₗ-rid* ∨ₗ-rann* λ _ → BType


 -- -- now define the join, don't think it works
 -- _∧ₗ_ : ZarLat → ZarLat → ZarLat
 -- _∧ₗ_ = Rec.f (isSetΠ (λ _ → trunc)) D[_]∧ₗ -- base case in the left argument
 --                                     (λ d∧ₗ_ e∧ₗ_ g → (d∧ₗ g) ∨ₗ (e∧ₗ g))
 --                                     -- distributivity holds judgmentally
 --                                     {!!} {!!} {!!} {!!} {!!} {!!}
 --  where
 --  D[_]∧ₗ : A → ZarLat → ZarLat
 --  -- defines (D x) ∧ₗ_
 --  D[ x ]∧ₗ = Rec.f trunc (λ y → D (x · y)) -- (D x) ∧ₗ (D y) ≡ D (x · y) holds definitionally
 --                         _∨ₗ_ -- defines (D x) ∧ₗ (d ∨ₗ e) by applying D[x]∧ₗ_ to d and e
 --                              -- before using ∨ₗ, i.e. we get distributivity judgmentally
 --                         Dx∧ₗ-path-+≤∨
 --                         {!!} {!!} {!!} {!!} {!!}
 --   where
 --   Dx∧ₗ-path-+≤∨ : ∀ y z → D (x · (y + z)) ≡ D (x · (y · (y + z))) ∨ₗ D (x · (z · (y + z)))
 --   Dx∧ₗ-path-+≤∨ y z = {!!}
 --   -- let path : ∀ x y z →  y · (x · y + x · z) ≡ x · (y · (y + z))
 --   --     path = solve A'
 --   -- in cong D (·Rdist+ x y z) ∙∙ +≤∨ (x · y) (x · z) ∙∙ {!!}
