{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.RingedLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

-- open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

-- open import Cubical.Displayed.Base
-- open import Cubical.Displayed.Auto
-- open import Cubical.Displayed.Record
-- open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
-- open import Cubical.Algebra.DistLattice.DownSet
-- open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
-- open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Poset

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

-- open import Cubical.Relation.Binary
-- open import Cubical.Relation.Binary.Poset

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.RingedLattice.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
  open RingedLattice
  open RingedLatticeHom

  compRingedLatticeHom : (X : RingedLattice ℓ) (Y : RingedLattice ℓ') (Z : RingedLattice ℓ'')
                       → RingedLatticeHom X Y → RingedLatticeHom Y Z → RingedLatticeHom X Z
  π (compRingedLatticeHom X Y Z f g) = compDistLatticeHom _ _ _ (f .π) (g .π)
  π♯ (compRingedLatticeHom X Y Z f g) u = compCommRingHom _ _ _ (f .π♯ u) (g .π♯ (f .π .fst u))
  isNatπ♯ (compRingedLatticeHom X Y Z f g) u v u≥v =
    (g .π♯ (f .π .fst v) ∘cr (f .π♯ v)) ∘cr X .𝓕 .Functor.F-hom u≥v ≡⟨ {!!} ⟩
    (Z .𝓕 .Functor.F-hom (pres≤ (g .π ∘dl f .π) u≥v)) ∘cr (g .π♯ (f .π .fst u) ∘cr f .π♯ u) ∎

  _∘rl_ : {X : RingedLattice ℓ} {Y : RingedLattice ℓ'} {Z : RingedLattice ℓ''}
        → RingedLatticeHom Y Z → RingedLatticeHom X Y → RingedLatticeHom X Z
  g ∘rl f = compRingedLatticeHom _ _ _ f g

  -- compIdRingedLatticeHom : {X Y : RingedLattice ℓ} (f : RingedLatticeHom X Y)
  --                        → compRingedLatticeHom _ _ _ (idRingedLatticeHom X) f ≡ f
  -- compIdRingedLatticeHom = ?

  -- idCompRingedLatticeHom : {X Y : RingedLattice ℓ} (f : RingedLatticeHom X Y)
  --                        → compRingedLatticeHom _ _ _ f (idRingedLatticeHom Y) ≡ f
  -- idCompRingedLatticeHom = ?

  -- compAssocRingedLatticeHom : {X Y Z U : RingedLattice ℓ}
  --                             (f : RingedLatticeHom X Y)
  --                             (g : RingedLatticeHom Y Z)
  --                             (h : RingedLatticeHom Z U)
  --                           → compRingedLatticeHom _ _ _ (compRingedLatticeHom _ _ _ f g) h
  --                           ≡ compRingedLatticeHom _ _ _ f (compRingedLatticeHom _ _ _ g h)
  -- compAssocRingedLatticeHom = {!!}
