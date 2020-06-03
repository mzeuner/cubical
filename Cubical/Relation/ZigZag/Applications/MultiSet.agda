-- We apply the theory of zigzag complete relations to finite multisets and association lists.
-- See discussion at the end of the file.
{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.ZigZag.Applications.MultiSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic hiding ([_])
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Empty as ⊥
open import Cubical.Structures.MultiSet
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.ZigZag.Base as ZigZag



private
 variable
  ℓ : Level
  A : Type ℓ


-- we define simple association lists without any higher constructors
data AList (A : Type ℓ) : Type ℓ where
 ⟨⟩ : AList A
 ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_


AListFinConcat : (n : ℕ) (f : Fin n → A) (g : Fin n → ℕ) → AList A
AListFinConcat zero f g = ⟨⟩
AListFinConcat (suc n) f g = ⟨ f zero , g zero ⟩∷ AListFinConcat n f' g'
 where
 f' = λ ind → f (suc ind)
 g' = λ ind → g (suc ind)



-- Yet another way of defining finite multisets:
supp : {A : Type ℓ} → (A → ℕ) → Type ℓ
supp {A = A} f = Σ[ a ∈ A ] (0 < f a)

fin-supp : {A : Type ℓ} → (A → ℕ) → Type ℓ
fin-supp f = Σ[ n ∈ ℕ ] (Fin n ≃ supp f)

-- untruncated version:
FFMS : (A : Type ℓ) → Type ℓ
FFMS A = Σ[ f ∈ (A → ℕ) ] fin-supp f

FuncFMS : (A : Type ℓ) → Type ℓ
FuncFMS A = Σ[ f ∈ (A → ℕ) ] ∥ fin-supp f ∥


Set-PropTrunc-lemma : {X Y : Type ℓ} {P : X → Type ℓ} (Yset : isSet Y)
                  → (φ : (x : X) → P x → Y)
                  → (ρ : (x : X) → (α β : P x) → φ x α ≡ φ x β)
                  -----------------------------------------------------
                  → (x : X) → ∥ P x ∥ → Y
Set-PropTrunc-lemma Yset φ ρ x = elim→Set (λ _ → Yset) (λ α → φ x α) (λ α β → ρ x α β)





-- We have a count-structure on List and AList and use these to get a bisimulation between the two
module Lists&ALists {A : Type ℓ} (discA : Discrete A) where
 -- the relation we're interested in
 S = count-structure A (Discrete→isSet discA)
 R : {A B : TypeWithStr ℓ S} → (A .fst) → (B .fst) → Type ℓ
 R {X , count₁} {Y , count₂} x y = ∀ a → count₁ a x ≡ count₂ a y

 -- relation between R and ι
 ι = count-iso A (Discrete→isSet discA)
 ι-R-char : {X Y : TypeWithStr ℓ S} (e : (X .fst) ≃ (Y .fst))
          → (∀ x → R {X} {Y} x (e .fst x)) ≃ (ι X Y e)
 ι-R-char e = isoToEquiv (iso (λ f → λ a x → f x a) (λ g → λ x a → g a x) (λ _ → refl) λ _ → refl)

 -- some results about R
 module R-char {(X , Xcount) (Y , Ycount) : TypeWithStr ℓ S}
               {f : X → Y} {g : Y → X}
               {isBisimRfg : isBisimulation (R {X , Xcount} {Y , Ycount}) f g} where

  Rˣ = ZigZag.Bisimulation→Equiv.Rᴬ X Y (R {X , Xcount} {Y , Ycount}) f g isBisimRfg

  to : ∀ {x} {x'} → (∀ a → Xcount a x ≡ Xcount a x') → Rˣ x x'
  to {x} {x'} ρ = f x , isBisimRfg .snd .fst x , λ a → sym (ρ a) ∙ isBisimRfg .snd .fst x a

  from : ∀ {x} {x'} → Rˣ x x' → ∀ a → Xcount a x ≡ Xcount a x'
  from {x} {x'} r a = r .snd .fst a ∙ sym (r .snd .snd a)




 -- helper function for count-structures for (association) lists
 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n


 -- the count-structures
 Lcount : S (List A)
 Lcount a [] = zero
 Lcount a (x ∷ xs) = aux a x (discA a x) (Lcount a xs)

 ALcount : S (AList A)
 ALcount a ⟨⟩ = zero
 ALcount a (⟨ x , zero ⟩∷ xs) = ALcount a xs
 ALcount a (⟨ x , suc n ⟩∷ xs) = aux a x (discA a x) (ALcount a (⟨ x , n ⟩∷ xs))


 -- now for the bisimulation between List and Alist
 φ : List A → AList A
 φ [] = ⟨⟩
 φ (x ∷ xs) = ⟨ x , 1 ⟩∷ φ xs

 ψ : AList A → List A
 ψ ⟨⟩ = []
 ψ (⟨ x , zero ⟩∷ xs) = ψ xs
 ψ (⟨ x , suc n ⟩∷ xs) = x ∷ ψ (⟨ x , n ⟩∷ xs)


 η : ∀ x → R {List A , Lcount} {AList A , ALcount} x (φ x)
 η [] a = refl
 η (x ∷ xs) a  with (discA a x)
 ...           | yes a≡x = cong suc (η xs a)
 ...           | no  a≢x = η xs a


 -- for the other direction we need a little helper function
 ε : ∀ y → R {List A , Lcount} {AList A , ALcount} (ψ y) y
 ε' : (x : A) (n : ℕ) (xs : AList A) (a : A)
    → Lcount a (ψ (⟨ x , n ⟩∷ xs)) ≡ ALcount a (⟨ x , n ⟩∷ xs)

 ε ⟨⟩ a = refl
 ε (⟨ x , n ⟩∷ xs) a = ε' x n xs a

 ε' x zero xs a = ε xs a
 ε' x (suc n) xs a with discA a x
 ...                 | yes a≡x = cong suc (ε' x n xs a)
 ...                 | no  a≢x = ε' x n xs a


 -- R {List A , Lcount} {AList A , ALcount} is zigzag-complete
 zigzagR : isZigZagComplete (R {List A , Lcount} {AList A , ALcount})
 zigzagR _ _ _ _ r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)


 -- now we can apply the main result about zigzag-complete relations:
 Rᴸ  = ZigZag.Bisimulation→Equiv.Rᴬ (List A) (AList A) (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)
 Rᴬᴸ = ZigZag.Bisimulation→Equiv.Rᴮ (List A) (AList A) (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)

 List/Rᴸ = (List A) / Rᴸ
 AList/Rᴬᴸ = (AList A) / Rᴬᴸ


 List/Rᴸ≃AList/Rᴬᴸ : List/Rᴸ ≃ AList/Rᴬᴸ
 List/Rᴸ≃AList/Rᴬᴸ = ZigZag.Bisimulation→Equiv.Thm (List A) (AList A)
                                                   (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)

 --We want to show that this is an isomorphism of count-structures.
 --For this we first have to define the count-functions
 LQcount : A → List/Rᴸ → ℕ
 LQcount a [ xs ] = Lcount a xs
 LQcount a (eq/ xs ys r i) = ρ a i
  where
  ρ : ∀ a → Lcount a xs ≡ Lcount a ys
  ρ a = (r .snd .fst a) ∙ sym (r .snd .snd a)
 LQcount a (squash/ xs/ xs/₁ p q i j) =
         isSetℕ (LQcount a xs/) (LQcount a xs/₁) (cong (LQcount a) p) (cong (LQcount a) q) i j


 ALQcount : A → AList/Rᴬᴸ → ℕ
 ALQcount a [ xs ] = ALcount a xs
 ALQcount a (eq/ xs ys r i) = ρ a i
  where
  ρ : ∀ a → ALcount a xs ≡ ALcount a ys
  ρ a = sym (r .snd .fst a) ∙ (r .snd .snd a)
 ALQcount a (squash/ xs/ xs/₁ p q i j) =
          isSetℕ (ALQcount a xs/) (ALQcount a xs/₁) (cong (ALQcount a) p) (cong (ALQcount a) q) i j

 -- We get that the equivalence is an isomorphism directly from the fact that is induced by a bisimulation
 -- and the fact that we can characterize ι (count-iso) in terms of R through the following observation
 -- ξ = List/Rᴸ≃AList/Rᴬᴸ .fst
 -- observation : (xs : List A) → R {List/Rᴸ , LQcount} {AList/Rᴬᴸ , ALQcount} [ xs ] (ξ [ xs ])
 -- observation = η

 List/Rᴸ≃AList/Rᴬᴸ-is-count-iso : ι (List/Rᴸ , LQcount) (AList/Rᴬᴸ , ALQcount) List/Rᴸ≃AList/Rᴬᴸ
 List/Rᴸ≃AList/Rᴬᴸ-is-count-iso = ι-R-char {Y = (AList/Rᴬᴸ , ALQcount)} List/Rᴸ≃AList/Rᴬᴸ .fst
                                  (elimProp (λ _ → isPropΠ (λ _ → isSetℕ _ _)) η)


 -- We now show that List/Rᴸ≃FMSet
 _∷/_ : A → List/Rᴸ → List/Rᴸ
 a ∷/ [ xs ] = [ a ∷ xs ]
 a ∷/ eq/ xs xs' r i = eq/ (a ∷ xs) (a ∷ xs') r' i
  where
  r' : Rᴸ (a ∷ xs) (a ∷ xs')
  r' =  ⟨ a , 1 ⟩∷ (r .fst)
      , (λ a' → cong (aux a' a (discA a' a)) (r .snd .fst a'))
      , (λ a' → cong (aux a' a (discA a' a)) (r .snd .snd a'))
 a ∷/ squash/ xs xs₁ p q i j = squash/ (a ∷/ xs) (a ∷/ xs₁) (cong (a ∷/_) p) (cong (a ∷/_) q) i j

 infixr 5 _∷/_

 μ : FMSet A → List/Rᴸ
 μ = FMS.Rec.f squash/ [ [] ] _∷/_ β
  where
  β : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
  β a b = elimProp (λ _ → squash/ _ _) (λ xs → eq/ _ _ (γ xs))
   where
     γ : ∀ xs → Rᴸ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
     γ xs = φ (a ∷ b ∷ xs) , η (a ∷ b ∷ xs) , λ c → sym (δ c) ∙ η (a ∷ b ∷ xs) c
      where
      δ : ∀ c → Lcount c (a ∷ b ∷ xs) ≡ Lcount c (b ∷ a ∷ xs)
      δ c with discA c a | discA c b
      δ c | yes _        | yes _ = refl
      δ c | yes _        | no  _ = refl
      δ c | no  _        | yes _ = refl
      δ c | no  _        | no  _ = refl


 -- The inverse is induced by the standard projection of lists into finite multisets,
 -- which is a morphism of count-structures
 -- Moreover, we need 'count-extensionality' for finite multisets
 List→FMSet : List A → FMSet A
 List→FMSet [] = []
 List→FMSet (x ∷ xs) = x ∷ List→FMSet xs

 List→FMSet-count : ∀ a xs → Lcount a xs ≡ FMScount discA a (List→FMSet xs)
 List→FMSet-count a [] = refl
 List→FMSet-count a (x ∷ xs) with discA a x
 ...                         | yes _ = cong suc (List→FMSet-count a xs)
 ...                         | no  _ = List→FMSet-count a xs


 ν : List/Rᴸ → FMSet A
 ν [ xs ] = List→FMSet xs
 ν (eq/ xs ys r i) = path i
  where
   ρ : ∀ a → Lcount a xs ≡ Lcount a ys
   ρ = λ a → (r .snd .fst a) ∙ sym (r .snd .snd a)

   θ : ∀ a → FMScount discA a (List→FMSet xs) ≡ FMScount discA a (List→FMSet ys)
   θ a = sym (List→FMSet-count a xs) ∙∙ ρ a ∙∙ List→FMSet-count a ys

   path : List→FMSet xs ≡ List→FMSet ys
   path = FMScountExt.Thm discA _ _ θ
 ν (squash/ xs/ xs/' p q i j) = trunc (ν xs/) (ν xs/') (cong ν p) (cong ν q) i j


 σ : section μ ν
 σ = elimProp (λ _ → squash/ _ _) θ
  where
  θ : (xs : List A) → μ (ν [ xs ]) ≡ [ xs ]
  θ [] = refl
  θ (x ∷ xs) = cong (x ∷/_) (θ xs)


 ν-∷/-commute : (x : A) (ys : List/Rᴸ) → ν (x ∷/ ys) ≡ x ∷ ν ys
 ν-∷/-commute x = elimProp (λ _ → FMS.trunc _ _) λ xs → refl

 τ : retract μ ν
 τ = FMS.ElimProp.f (FMS.trunc _ _) refl θ
  where
  θ : ∀ x {xs} → ν (μ xs) ≡ xs → ν (μ (x ∷ xs)) ≡ x ∷ xs
  θ x {xs} p = ν-∷/-commute x (μ xs) ∙ cong (x ∷_) p


 FMSet≃List/Rᴸ : FMSet A ≃ List/Rᴸ
 FMSet≃List/Rᴸ = isoToEquiv (iso μ ν σ τ)

 --and this is a count-isomorphism, which is easier to prove for the inverse equiv
 List/Rᴸ≃FMSet : List/Rᴸ ≃ FMSet A
 List/Rᴸ≃FMSet = isoToEquiv (iso ν μ τ σ)

 List/Rᴸ≃FMSet-is-count-iso : ι (List/Rᴸ , LQcount) (FMSet A , FMScount discA) List/Rᴸ≃FMSet
 List/Rᴸ≃FMSet-is-count-iso = ι-R-char {Y = (FMSet A , FMScount discA)} List/Rᴸ≃FMSet .fst
                              (elimProp (λ _ → isPropΠ (λ _ → isSetℕ _ _)) λ xs a → List→FMSet-count a xs)


 {-
 Putting everything together we get:

               ≃
 List/Rᴸ ------------> AList/Rᴬᴸ

   |
   |≃
   |
   ∨
               ≃
 FMSet A ------------> AssocList A


 We thus get that AList/Rᴬᴸ≃AssocList.
 Constructing such an equivalence directly requires count extensionality for association lists,
 which should be even harder to prove than for finite multisets.

 This strategy should work for all implementations of multisets with HITs.
 We just have to show that:

  ∙ The HIT is equivalent to FMSet (like AssocList)
  ∙ There is a bisimulation between lists and the basic data type of the HIT
    with the higher constructors removed (like AList)

 Then we get that this HIT is equivalent to the corresponding set quotient that identifies elements
 that give the same count on each a : A.

 TODO: Show that all the equivalences are indeed isomorphisms of multisets not only of count-structures!
 -}



 -- We establish a bisimulation between AList and FFMS (the untruncated version)
 ξ : FFMS A → AList A
 ξ (f , n , e) = AListFinConcat n (λ ind → (e .fst ind) .fst) (λ ind → f ((e .fst ind) .fst))

 ζ : AList A → FFMS A
 ζ xs = (λ a → ALcount a xs) , {!!} , {!!}

 -- ξ-lemma : (n : ℕ) (f : A → ℕ) (e : Fin n ≃ supp f) → ∀ a → ALcount a (ξ f (n , e)) ≡ f a
 -- ξ-lemma zero f e a with zero ≟ f a
 -- ...                | lt 0<fa = ⊥.rec (¬Fin0 (invEquiv e .fst (a , 0<fa)))
 -- ...                | eq 0≡fa = 0≡fa
 -- ...                | gt 0>fa = ⊥.rec (¬-<-zero 0>fa)
 -- ξ-lemma (suc n) f e a = cong (ALcount a) path ∙ eq₁
 --  where
 --  ys = ξ f (suc n , e)
 --  a₀ = (e .fst zero) .fst

 --  g : A → ℕ
 --  g a' with discA  a' a₀
 --  ...  | yes _ = zero
 --  ...  | no  _ = f a'

 --  e' : Fin n ≃ supp g
 --  fst e' ind = e .fst (suc ind) .fst , {!!}
 --  snd e' = {!!}

 --  β : fin-supp g
 --  β = (n , e')

 --  xs = ξ g β

 --  hyp : ∀ a → ALcount a xs ≡ g a
 --  hyp = ξ-lemma n g e'

 --  path : ys ≡ ⟨ a₀ , f a₀ ⟩∷ xs
 --  path = cong (⟨ a₀ , f a₀ ⟩∷_) {!!}

 --  eq₁ : ALcount a (⟨ a₀ , f a₀ ⟩∷ xs) ≡ f a
 --  eq₁ with discA a a₀
 --  ... | yes a≡a₀ = {!!}
 --  ... | no  a≢a₀ = ALcount a (⟨ a₀ , f a₀ ⟩∷ xs) ≡⟨ {!refl!} ⟩
 --                   ALcount a xs ≡⟨ hyp a ⟩
 --                   g a ≡⟨ eq₂ ⟩
 --                   f a ∎
 --   where
 --   eq₂ : g a ≡ f a
 --   eq₂  with discA a a₀
 --   ... | yes a≡a₀ = ⊥.rec (a≢a₀ a≡a₀)
 --   ... | no  a≢a₀ = refl



 -- Ξ : FuncFMS A →  AList/Rᴬᴸ
 -- Ξ (f , |finsuppf|) = Set-PropTrunc-lemma {P = fin-supp} squash/ (λ f α → [ ξ f α ]) θ f |finsuppf|
 --  where
 --  θ : (f : A → ℕ) (α β : fin-supp f) → [ ξ f α ] ≡ [ ξ f β ]
 --  θ f α β = eq/ _ _ (ψ (ξ f α)
 --                   , ε (ξ f α)
 --                   , λ a → ε (ξ f α) a ∙∙ ξ-lemma (α .fst) f (α .snd) a ∙∙ sym (ξ-lemma (β .fst) f (β .snd) a))

