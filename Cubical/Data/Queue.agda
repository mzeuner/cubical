{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue where

open import Cubical.Foundations.Everything

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Prod.Base hiding (_×_ ; map-×) renaming (_×Σ_ to _×_)


-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

variable
 ℓ ℓ' : Level

-- Two necessary result to define a queue isomorphism
map⃗ : {A : Type ℓ} {B : Type ℓ'} (f : A ≃ B)
       → (A → A) → (B → B)
map⃗ f g b = fst f (g (fst (invEquiv f) b))
-- Do we need that map-→ f is an equivalence?

map-× : {A B C D : Type ℓ} → (A → B) → (C → D) → (A × C) → (B × D)
map-× f g (a , c) = f a , g c

queue-structure : Type ℓ → Type (ℓ-suc ℓ)
queue-structure {ℓ = ℓ} A = Σ (Type ℓ) (λ Q →     Q
                                            × (A → Q → Q)
                                            × (Q → (Unit ⊎ (Q × A))))
Queue : Type (ℓ-max ℓ (ℓ-suc ℓ))
Queue {ℓ = ℓ} = Σ (Type ℓ) λ A → queue-structure A

-- queue-iso : (X Y : Queue) → (fst X) ≃ (fst Y) → Type ℓ
-- queue-iso {ℓ = ℓ} X Y e = {!!}
