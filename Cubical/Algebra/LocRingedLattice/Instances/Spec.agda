{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.LocRingedLattice.Instances.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.DownSet

open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty
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

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level


module _ (R : CommRing ℓ) where
  open ZarLat
  open ZarLatUniversalProp R
  open LocRingedLattice
  open Order (DistLattice→Lattice (ZariskiLattice R))
  open PosetStr using (is-prop-valued)
  open InvertingElementsBase R

  private
    BOPoset = MeetSemilattice.IndPoset
                (Basis→MeetSemilattice (ZariskiLattice R) (BasicOpens R) (basicOpensAreBasis R))

    BOPosetIncl : Functor (PosetCategory BOPoset) (ZariskiCat R)
    BOPosetIncl = B↪L _ _ (basicOpensAreBasis R) _ (isSheaf𝓞 R)

    Dᴮᴼ : R .fst → BO R
    Dᴮᴼ f = D f , ∣ f , refl ∣₁


    BOPropElim : {P : BO R → Type ℓ'}
               → (∀ x → isProp (P x))
               → (∀ f → P (Dᴮᴼ f))
    -----------------------------------
               → ∀ x → P x
    BOPropElim {P = P} isPropP PDᴮᴼ = uncurry curriedHelper
      where
      curriedHelper : ∀ (𝔞 : ZL R) (p : 𝔞 ∈ BasicOpens R) → P (𝔞 , p)
      curriedHelper 𝔞 = PT.elim (λ _ → isPropP _) truncHelper
        where
        truncHelper : ∀ p → P (𝔞 , ∣ p ∣₁)
        truncHelper (f , p) = subst P path (PDᴮᴼ f)
          where
          path : Dᴮᴼ f ≡ (𝔞 , ∣ f , p ∣₁)
          path = Σ≡Prop (λ _ → isPropPropTrunc) p


  open PosetDownset BOPoset

  -- 𝓓base : (f : R .fst) → R[1/ f ] → ↓ (Dᴮᴼ f)
  -- 𝓓base = {!!} -- s.t. this is a InvSup ,but how to state with posets and presheaves?

  -- 𝓓ᴮᴼ : (u : BO R) → 𝓞 R .F-ob (u .fst) .fst → ↓ u
  -- 𝓓ᴮᴼ = {!!}

  BOInvMapAtStageDᴮᴼ : ∀ f → InvMapAtStage BOPoset (𝓞 R ∘F (BOPosetIncl ^opF)) (Dᴮᴼ f)
  BOInvMapAtStageDᴮᴼ f = foo , {!!}
    where
    foo : 𝓞 R .F-ob (D f) .fst → ↓ (Dᴮᴼ f)
    foo = {!!}

  BOInvMap : InvMap BOPoset (𝓞 R ∘F (BOPosetIncl ^opF))
  BOInvMap = InvMapAtStage→InvMap _ _
               (BOPropElim (λ _ → isPropInvMapAtStage _ _ _) BOInvMapAtStageDᴮᴼ)

  ZLInvMap : InvMap _ (𝓞 R)
  ZLInvMap = InvMapFromBasis _ _ (basicOpensAreBasis R) _ (isSheaf𝓞 R) (BOInvMap .fst) (BOInvMap .snd)

  DLSpec : LocRingedLattice ℓ
  L DLSpec = ZariskiLattice R
  𝓕 DLSpec = 𝓞 R
  isSheaf𝓕 DLSpec = isSheaf𝓞 R
  𝓓 DLSpec = ZLInvMap .fst
  isInvMap𝓓 DLSpec = ZLInvMap .snd
  isSupport𝓓 DLSpec = {!!}
