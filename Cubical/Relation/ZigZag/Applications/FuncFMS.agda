{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.ZigZag.Applications.FuncFMS where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Structures.MultiSet
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
-- open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
open import Cubical.HITs.AssocList as AL
open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.HITs.ListedFiniteSet as LFS
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.ZigZag.Base as ZigZag

private
 variable
  ℓ : Level
  A : Type ℓ

_holds : hProp ℓ → Type ℓ
_holds = fst

module _(A : Type₀) (discA : Discrete A) where

 ∈-dec : (a : A) (xs : LFSet A) → Dec ((a ∈ xs) .fst)
 ∈-dec a = LFS.PropElim.f _ (no λ x → x) ρ λ xs → isPropDec ((a ∈ xs) .snd)
  where
  ρ : (x : A) {xs : LFSet A} → Dec ((a ∈ xs) .fst)
                             → Dec ((a ∈ (x ∷ xs)) .fst)
  ρ x (yes a∈xs) = yes (∣ inr a∈xs ∣)
  ρ x {xs} (no  a∉xs) with discA a x
  ...                 | yes a≡x = yes ∣ inl (∣ a≡x ∣) ∣
  ...                 | no  a≢x = no (PT.rec isProp⊥ foo)
   where
   foo : ∥ a ≡ x ∥ ⊎ (a ∈ xs) .fst → ⊥
   foo (inl p) = PT.rec isProp⊥ (λ a≡x → ⊥.rec (a≢x a≡x)) p
   foo (inr a∈xs) = ⊥.rec (a∉xs a∈xs)


 _∈ᵈ_ : A → LFSet A → Bool
 a ∈ᵈ xs with ∈-dec a xs
 ...     | yes a∈xs = true
 ...     | no  a∉xs = false


 -- rm-dup : LFSet A → FMSet A
 -- rm-dup LFS.[] = FMS.[]
 -- rm-dup (x LFS.∷ xs) = {!!}
 -- rm-dup (dup x xs i) = {!!}
 -- rm-dup (comm x y xs i) = {!!}
 -- rm-dup (trunc xs xs₁ x y i i₁) = {!!}


 ξ : (A → ℕ) → LFSet A → AssocList A
 ξ f [] = ⟨⟩
 ξ f (x ∷ xs) with ∈-dec x xs
 ...              | yes x∈xs = ξ f xs
 ...              | no  x∉xs = ⟨ x , f x ⟩∷ ξ f xs
 ξ f (dup x xs i) = {!!}
  where
  path : ξ f (x ∷ x ∷ xs) ≡ ξ f (x ∷ xs)
  path = {!!}
 ξ f (comm x y xs i) = {!!}
 ξ f (trunc xs ys p q i j) = trunc (ξ f xs) (ξ f ys) (cong (ξ f) p) (cong (ξ f) q) i j


 max : ℕ → ℕ → ℕ
 max zero m = m
 max (suc n) zero = suc n
 max (suc n) (suc m) = suc (max m n)

 max-trans : ∀ m n k → max (max m n) k ≡ max m (max n k)
 max-trans zero n k = refl
 max-trans (suc m) zero k = refl
 max-trans (suc m) (suc n) zero = refl
 max-trans (suc m) (suc n) (suc k) = cong suc (sym (max-trans k n m))
