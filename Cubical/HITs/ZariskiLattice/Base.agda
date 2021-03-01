
{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.HITs.ZariskiLattice.Base where

--open import Cubical.Core.Primitives renaming (_∧_ to primIMin ; _∨_ to primIMax)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
-- open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
--                                       ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
--                                       ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
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
open import Cubical.Algebra.RingSolver.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level

module _ (A' : CommRing {ℓ}) where
 A = fst A'
 open CommRingStr (snd A')

 data ZarLat : Type ℓ where
   D : A → ZarLat
   _∨ₗ_ : ZarLat → ZarLat → ZarLat

   -- equivalent to D(x+y) ≤ D(x) ∨ D(y)
   +≤∨ : ∀ x y → D (x + y) ≡ D (x · (x + y)) ∨ₗ D (y · (x + y))

   ∨ₗ-idem : ∀ d → d ∨ₗ d ≡ d
   ∨ₗ-comm : ∀ d e → d ∨ₗ e ≡ e ∨ₗ d
   ∨ₗ-assoc : ∀ d e f →  d ∨ₗ (e ∨ₗ f) ≡ (d ∨ₗ e) ∨ₗ f
   ∨ₗ-rid : ∀ d → d ∨ₗ D 0r ≡ d
   ∨ₗ-rann : ∀ d → d ∨ₗ D 1r ≡ d

   trunc : isSet ZarLat

 -- module Elim {ℓ'} {B : ZarLat → Type ℓ'}
 --        (D* : (a : A) → B (D a)) (_∨ₗ_ : {d e : ZarLat} → B d → B e → B (d ∨ₗ e))
