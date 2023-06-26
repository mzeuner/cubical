{-# OPTIONS --safe #-}
module Cubical.Algebra.RingedLattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.DistLattice.Base

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

-- better as Σ?
record RingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ
    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕

open RingedLattice
-- why can't Y and X live in different universes?
RingeLatticeHom : RingedLattice ℓ → RingedLattice ℓ  → Type ℓ
RingeLatticeHom Y X = Σ[ f ∈ DistLatticeHom (Y .L) (X .L) ]
                        NatTrans (Y .𝓕) ((X .𝓕) ∘F ((DistLatticeFunc (Y .L) (X .L) f) ^opF))
