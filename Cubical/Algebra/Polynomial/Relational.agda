{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Algebra.Polynomial.Relational where
{-
  This file contains a relational approach to constructing polynomial rings.
  For a commut
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

open import Cubical.Structures.Relational.Auto
open import Cubical.Structures.Relational.Macro

private
 variable
  ℓ ℓ' : Level

open CommAlgebra

module _(R' : CommRing {ℓ}) (A₀' A₁' : CommAlgebra R')
        (eval₀ : (B : CommAlgebra R') → Carrier B → CommAlgebraHom A₀' B)
        (eval₁ : (B : CommAlgebra R') → Carrier B → CommAlgebraHom A₁' B)where
 private
  R = fst R'
  A₀ = Carrier A₀'
  A₁ = Carrier A₁'

 --open IsCommAlgebra {{...}}
 open AlgebraHom

 Rel : A₀ → A₁ → Type (ℓ-suc ℓ)
 Rel a₀ a₁ = ∀ (B : CommAlgebra R') (b : Carrier B) → f (eval₀ B b) a₀ ≡ f (eval₁ B b) a₁

 open CommAlgebraΣTheory R'
 open AlgebraΣTheory (CommRing→Ring R')
 module S = RelMacro ℓ (autoRelDesc RawAlgebraStructure)

 A₀RawStructure : RawAlgebraStructure A₀
 A₀RawStructure = CommAlgebra→CommAlgebraΣ A₀' .snd .fst

 A₁RawStructure : RawAlgebraStructure A₁
 A₁RawStructure = CommAlgebra→CommAlgebraΣ A₁' .snd .fst

 -- isStructuredRel : S.relation Rel A₀RawStructure A₁RawStructure
 -- isStructuredRel = ?
