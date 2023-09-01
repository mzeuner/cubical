{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.DistLattice where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Lattice

open Category

DistLatticeCategory : ∀ {ℓ} (L : DistLattice ℓ) → Category ℓ ℓ
DistLatticeCategory L = LatticeCategory (DistLattice→Lattice L)

--only need order preserving!!!!!!!
open Functor
DistLatticeFunc : ∀ {ℓ} {ℓ'} (L : DistLattice ℓ) (L' : DistLattice ℓ') (f : DistLatticeHom L L')
                → Functor (DistLatticeCategory L) (DistLatticeCategory L')
F-ob (DistLatticeFunc L L' f) = f .fst
F-hom (DistLatticeFunc L L' f) x≤y = sym (f .snd .IsLatticeHom.pres∨l _ _) ∙ cong (f .fst) x≤y
F-id (DistLatticeFunc L  L' f) = isSetDistLattice L' _ _ _ _
F-seq (DistLatticeFunc L L' f) _ _ = isSetDistLattice L' _ _ _ _
