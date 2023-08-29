{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.LocRingedLattice.Instances.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis

open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty renaming (IsZarMap to isSupport ; isPropIsZarMap to isPropIsSupport)
open import Cubical.Algebra.ZariskiLattice.StructureSheaf

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Poset

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.LocRingedLattice.Base
open import Cubical.Algebra.LocRingedLattice.Properties

open Iso
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level


module _ (R : CommRing ℓ) where
  open ZarLat
  open ZarLatUniversalProp
  open LocRingedLattice

  open Order (DistLattice→Lattice (ZariskiLattice R))

  open PosetStr using (is-prop-valued)

  private
    BOPoset = MeetSemilattice.IndPoset
                (Basis→MeetSemilattice (ZariskiLattice R) (BasicOpens R) (basicOpensAreBasis R))

    BOPosetIncl : Functor (PosetCategory BOPoset) (ZariskiCat R)
    BOPosetIncl = B↪L _ _ (basicOpensAreBasis R) _ (isSheaf𝓞 R)

  𝓓ᴮᴼ : (u : BO R) → 𝓞 R .F-ob (u .fst) .fst → BO R
  𝓓ᴮᴼ = {!!}

  IsInvMap𝓓ᴮᴼ : IsInvMap BOPoset (𝓞 R ∘F (BOPosetIncl ^opF)) 𝓓ᴮᴼ
  IsInvMap𝓓ᴮᴼ = {!!}

  ZLInvMap : InvMap _ (𝓞 R)
  ZLInvMap = InvMapFromBasis _ _ (basicOpensAreBasis R) _ (isSheaf𝓞 R) 𝓓ᴮᴼ IsInvMap𝓓ᴮᴼ

  DLSpec : LocRingedLattice ℓ
  L DLSpec = ZariskiLattice R
  𝓕 DLSpec = 𝓞 R
  isSheaf𝓕 DLSpec = isSheaf𝓞 R
  𝓓 DLSpec = ZLInvMap .fst
  isSupport𝓓 DLSpec = {!!}
  isInvMap𝓓 DLSpec = ZLInvMap .snd
