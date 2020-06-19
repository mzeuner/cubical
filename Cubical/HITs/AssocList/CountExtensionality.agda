{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.AssocList.CountExtensionality where

open import Cubical.HITs.AssocList.Base as AL
open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.HITs.FiniteMultiset.Properties as FMS
open import Cubical.HITs.FiniteMultiset.CountExtensionality as FMSCE
open import Cubical.HITs.AssocList.Base
open import Cubical.HITs.AssocList.Properties as AL
open import Cubical.Data.Nat   --using (ℕ; zero; suc; _+_; +-assoc; isSetℕ)
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    ℓ : Level
    A : Type ℓ


module transptest (A : Type ℓ) (discA : Discrete A) where
 ALremove1 : A → AssocList A → AssocList A
 ALremove1 a xs = transport⁻ AssocList≡FMSet (FMS.remove1 discA a (transport AssocList≡FMSet xs))


xs : AssocList ℕ
xs = ⟨ zero , 5 ⟩∷ ⟨⟩

ys : AssocList ℕ
ys = transptest.ALremove1 ℕ discreteℕ zero xs

zs : AssocList ℕ
zs = ⟨ zero , 4 ⟩∷ ⟨⟩

-- _ : ys ≡ zs
-- _ = refl
