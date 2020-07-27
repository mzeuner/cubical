{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.ZigZag.Applications.FuncFMS where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
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
  A : Type₀

_holds : hProp ℓ → Type ℓ
_holds = fst

record FFMS (A : Type₀) : Type₀ where
  no-eta-equality
  field
   fun : A → ℕ
   supp : LFSet A
   toSupp : ∀ a → 0 < fun a → (a ∈ supp) holds
   fromSupp : ∀ a → (a ∈ supp) holds → 0 < fun a

-- LFSet-++-char : {A : Type₀} {xs ys : LFSet A} (a : A) → (a ∈ (xs ++ ys)) .fst → ∥ (a ∈ xs) .fst ⊎ (a ∈ ys) .fst ∥
-- LFSet-++-char {A} {[]} {ys} a ∈++ = ∣ inr ∈++ ∣
-- LFSet-++-char {A} {x ∷ xs} {ys} a ∈++ = {!!}
-- LFSet-++-char {A} {dup x xs i} {ys} a ∈++ = {!!}
-- LFSet-++-char {A} {comm x y xs i} {ys} a ∈++ = {!!}
-- LFSet-++-char {A} {trunc xs xs₁ x y i i₁} {ys} a ∈++ = {!!}

infixr 5 _∪ᴹ_

open FFMS

<0-Dich : {m n : ℕ} → 0 < m + n → (0 < m) ⊎ (0 < n)
<0-Dich {zero} 0<m+n = inr 0<m+n
<0-Dich {suc m} _ = inl (m , +-comm m 1)


_∪ᴹ_ : FFMS A → FFMS A → FFMS A
fun (XS ∪ᴹ YS) a = XS .fun a + YS .fun a
supp (XS ∪ᴹ YS) = XS .supp ++ YS .supp
toSupp (XS ∪ᴹ YS) a  0<XSfa+YSfa = {!!}
fromSupp (XS ∪ᴹ YS) = {!!}

-- define intersection of LFSets and thus of FFMS, show equivalence with FMSet/AssocList
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
 a ∈ᵈ xs = Dec→Bool (∈-dec a xs)


 -- rm-dup : LFSet A → FMSet A
 -- rm-dup LFS.[] = FMS.[]
 -- rm-dup (x LFS.∷ xs) = {!!}
 -- rm-dup (dup x xs i) = {!!}
 -- rm-dup (comm x y xs i) = {!!}
 -- rm-dup (trunc xs xs₁ x y i i₁) = {!!}


 -- ξ : (A → ℕ) → LFSet A → AssocList A
 -- ξ f [] = ⟨⟩
 -- ξ f (x ∷ xs) = caseBool (ξ f xs) (⟨ x , f x ⟩∷ ξ f xs) (x ∈ᵈ xs)
 -- ξ f (dup x xs i) = path i
 --  where
 --  path : ξ f (x ∷ x ∷ xs) ≡ ξ f (x ∷ xs)
 --  path = {!!}
 -- ξ f (comm x y xs i) = {!!}
 -- ξ f (trunc xs ys p q i j) = trunc (ξ f xs) (ξ f ys) (cong (ξ f) p) (cong (ξ f) q) i j


 max : ℕ → ℕ → ℕ
 max zero m = m
 max (suc n) zero = suc n
 max (suc n) (suc m) = suc (max m n)

 max-trans : ∀ m n k → max (max m n) k ≡ max m (max n k)
 max-trans zero n k = refl
 max-trans (suc m) zero k = refl
 max-trans (suc m) (suc n) zero = refl
 max-trans (suc m) (suc n) (suc k) = cong suc (sym (max-trans k n m))
