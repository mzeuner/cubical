{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base hiding (_×_ ; map-×) renaming (_×Σ_ to _×_)

open import Cubical.Experiments.EscardoSIP hiding (SNS)

-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

variable
 ℓ ℓ' : Level

-- necessary result to define a queue isomorphism

map-× : {A B C D : Type ℓ} → (A → B) → (C → D) → (A × C) → (B × D)
map-× f g (a , c) = f a , g c

queue-structure : Type ℓ → Type (ℓ-suc ℓ)
queue-structure {ℓ = ℓ} A = Σ[ Q ∈ Type ℓ ] (   Q
                                            × (A × Q → Q)
                                            × (Q → Unit ⊎ (Q × A)))


Queue : Type (ℓ-max ℓ (ℓ-suc ℓ))
Queue {ℓ = ℓ} = Σ (Type ℓ) λ A → queue-structure A


queue-iso : (X Y : Queue {ℓ = ℓ}) → (fst X) ≃ (fst Y) → Type ℓ
queue-iso (A , Q₁ , emp₁ , push₁ , pop₁) (B , Q₂ , emp₂ , push₂ , pop₂) e =
 Σ[ f ∈ (Q₁ ≃ Q₂) ] (  (fst f emp₁ ≡ emp₂)
                     × (∀ aq → f .fst (push₁ aq) ≡ push₂ (map-× (e .fst) (f .fst) aq))
                     × (∀ q → map-⊎ (idfun Unit) (map-× (fst f) (fst e)) (pop₁ q) ≡ pop₂ (fst f q)))


Queue-is-SNS : SNS {ℓ = ℓ} queue-structure queue-iso
Queue-is-SNS  {X = X} (Q₁ , emp₁ , push₁ , pop₁) (Q₂ , emp₂ , push₂ , pop₂) =

            (Q₁ , emp₁ , push₁ , pop₁) ≡ (Q₂ , emp₂ , push₂ , pop₂)
            
   ≃⟨ pathToEquiv (pathSigma≡sigmaPath (Q₁ , emp₁ , push₁ , pop₁) (Q₂ , emp₂ , push₂ , pop₂)) ⟩
   
            Σ[ p ∈ (Q₁ ≡ Q₂) ] (transport (λ i → p i × (X × p i → p i) × (p i → Unit ⊎ (p i × X))) (emp₁ , push₁ , pop₁) ≡ (emp₂ , push₂ , pop₂))
            
   ≃⟨ {!!} ⟩
   
            Σ[ p ∈ (Q₁ ≡ Q₂) ] (  (transport p emp₁ ≡ emp₂)
                                × (transport (λ i → X × p i → p i) push₁ ≡ push₂)
                                × (transport (λ i → p i → Unit ⊎ (p i × X)) pop₁ ≡ pop₂))
                                
   ≃⟨ {!!} ⟩
   
            Σ[ f ∈ (Q₁ ≃ Q₂) ] (  (fst f emp₁ ≡ emp₂)
                                × (∀ xq → f .fst (push₁ xq) ≡ push₂ (map-× (idfun X) (f .fst) xq))
                                × (∀ q → map-⊎ (idfun Unit) (map-× (fst f) (idfun X)) (pop₁ q) ≡ pop₂ (fst f q)))
   ■

