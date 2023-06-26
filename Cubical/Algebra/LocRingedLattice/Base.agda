{-# OPTIONS --safe #-}
module Cubical.Algebra.LocRingedLattice.Base where

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

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Algebra.ZariskiLattice.UniversalProperty renaming (IsZarMap to isSupport)

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
open Functor

private
  variable
    ℓ ℓ' : Level

-- better as Σ?
record LocRingedLattice (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : DistLattice ℓ
    𝓕 : Functor ((DistLatticeCategory L) ^op) (CommRingsCategory {ℓ})
    isSheaf𝓕 : isDLSheaf L _ 𝓕
    𝓓 : (u : L .fst) → 𝓕 .F-ob u .fst → L .fst
    isSupport𝓓 : ∀ u → isSupport (𝓕 .F-ob u) L (𝓓 u)

  open Order (DistLattice→Lattice L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  field
    𝓓≤ : ∀ u s → 𝓓 u s ≤ u
    --𝓓Inv : ∀ u v s → (v ≤ 𝓓 u s) →

open LocRingedLattice
-- why can't Y and X live in different universes?
-- RingeLatticeHom : RingedLattice ℓ → RingedLattice ℓ  → Type ℓ
-- RingeLatticeHom Y X = Σ[ f ∈ DistLatticeHom (Y .L) (X .L) ]
--                         NatTrans (Y .𝓕) ((X .𝓕) ∘F ((DistLatticeFunc (Y .L) (X .L) f) ^opF))
