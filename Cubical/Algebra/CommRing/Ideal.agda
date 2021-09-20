{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
                             renaming ( --zero to ℕzero ; suc to ℕsuc
                                        _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-assoc to +ℕ-assoc ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Data.FinData hiding (rec ; elim)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = IdealsInRing (CommRing→Ring R)

module _ (Ring@(R , str) : CommRing ℓ) where
  open CommRingStr str
  makeIdeal : (I : R → hProp ℓ)
              → (+-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0r-closed : 0r ∈ I)
              → (·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I)
              → IdealsIn (R , str)
  makeIdeal I +-closed 0r-closed ·-closedLeft = I ,
    (record
       { +-closed = +-closed
       ; -closed = λ x∈I → subst-∈ I (useSolver _)
                             (·-closedLeft (- 1r) x∈I)
       ; 0r-closed = 0r-closed
       ; ·-closedLeft = ·-closedLeft
       ; ·-closedRight = λ r x∈I →
                       subst-∈ I
                             (·-comm r _)
                             (·-closedLeft r x∈I)
       })
       where useSolver : (x : R) → - 1r · x ≡ - x
             useSolver = solve Ring


-- better?
module CommIdeal (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')

 record isCommIdeal (I : ℙ R) : Type ℓ where
  constructor
   makeIsCommIdeal
  field
   +Closed : ∀ {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
   contains0 : 0r ∈ I
   ·Closed : ∀ {x : R} (r : R) → x ∈ I → r · x ∈ I

 open isCommIdeal
 isPropIsCommIdeal : (I : ℙ R) → isProp (isCommIdeal I)
 +Closed (isPropIsCommIdeal I ici₁ ici₂ i) x∈I y∈I =
         I _ .snd (ici₁ .+Closed x∈I y∈I) (ici₂ .+Closed x∈I y∈I) i
 contains0 (isPropIsCommIdeal I ici₁ ici₂ i) = I 0r .snd (ici₁ .contains0) (ici₂ .contains0) i
 ·Closed (isPropIsCommIdeal I ici₁ ici₂ i) r x∈I =
         I _ .snd (ici₁ .·Closed r x∈I) (ici₂ .·Closed r x∈I) i

 CommIdeal : Type _
 CommIdeal = Σ[ I ∈ ℙ R ] isCommIdeal I

 ∑Closed : (I : CommIdeal) {n : ℕ} (V : FinVec R n)
         → (∀ i → V i ∈ fst I) → ∑ V ∈ fst I
 ∑Closed I {n = zero} _ _ = I .snd .contains0
 ∑Closed I {n = suc n} V h = I .snd .+Closed (h zero) (∑Closed I (V ∘ suc) (h ∘ suc))

 0Ideal : CommIdeal
 fst 0Ideal x = (x ≡ 0r) , is-set _ _
 +Closed (snd 0Ideal) x≡0 y≡0 = cong₂ (_+_) x≡0 y≡0 ∙ +Rid _
 contains0 (snd 0Ideal) = refl
 ·Closed (snd 0Ideal) r x≡0 = cong (r ·_) x≡0 ∙ 0RightAnnihilates _

 _+i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I +i J) x =
     (∃[ (y , z) ∈ (R × R) ] ((y ∈ I .fst) × (z ∈ J .fst) × (x ≡ y + z))) --have a record for this?
     , isPropPropTrunc
 +Closed (snd (I +i J)) {x = x₁} {y = x₂} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I .fst) × (z₁ ∈ J .fst) × (x₁ ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I .fst) × (z₂ ∈ J .fst) × (x₂ ≡ y₂ + z₂))
           → Σ[ (y₃ , z₃) ∈ (R × R) ] ((y₃ ∈ I .fst) × (z₃ ∈ J .fst) × (x₁ + x₂ ≡ y₃ + z₃))
  +ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x₁≡y₁+z₁) ((y₂ , z₂) , y₂∈I , z₂∈J , x₂≡y₂+z₂) =
    (y₁ + y₂ , z₁ + z₂) , +Closed (snd I) y₁∈I y₂∈I , +Closed (snd J) z₁∈J z₂∈J
                      , cong₂ (_+_) x₁≡y₁+z₁ x₂≡y₂+z₂ ∙ +ShufflePairs _ _ _ _
 contains0 (snd (I +i J)) = ∣ (0r , 0r) , contains0 (snd I) , contains0 (snd J) , sym (+Rid _) ∣
 ·Closed (snd (I +i J)) {x = x} r = map ·ClosedΣ
  where
  ·ClosedΣ : Σ[ (y₁ , z₁) ∈ (R × R) ] ((y₁ ∈ I .fst) × (z₁ ∈ J .fst) × (x ≡ y₁ + z₁))
           → Σ[ (y₂ , z₂) ∈ (R × R) ] ((y₂ ∈ I .fst) × (z₂ ∈ J .fst) × (r · x ≡ y₂ + z₂))
  ·ClosedΣ ((y₁ , z₁) , y₁∈I , z₁∈J , x≡y₁+z₁) =
    (r · y₁ , r · z₁) , ·Closed (snd I) r y₁∈I , ·Closed (snd J) r z₁∈J
                     , cong (r ·_) x≡y₁+z₁ ∙ ·Rdist+ _ _ _

 infixl 6 _+i_

 +iComm⊆ : ∀ (I J : CommIdeal) → (I +i J) .fst ⊆ (J +i I) .fst
 +iComm⊆ I J x = map λ ((y , z) , y∈I , z∈J , x≡y+z) → (z , y) , z∈J , y∈I , x≡y+z ∙ +Comm _ _

 +iComm : ∀ (I J : CommIdeal) → I +i J ≡ J +i I
 +iComm I J = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (+iComm⊆ I J , +iComm⊆ J I))

 +iLid : ∀ (I : CommIdeal) → 0Ideal +i I ≡ I
 +iLid I = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (incl1 , incl2))
  where
  incl1 : (0Ideal +i I) .fst ⊆ I .fst
  incl1 x = rec (I .fst x .snd) λ ((y , z) , y≡0 , z∈I , x≡y+z)
                                  → subst-∈ (fst I) (sym (x≡y+z ∙∙ cong (_+ z) y≡0 ∙∙ +Lid z)) z∈I

  incl2 : I .fst ⊆ (0Ideal +i I) .fst
  incl2 x x∈I = ∣ (0r , x) , refl , x∈I , sym (+Lid _) ∣

 +iLincl : ∀ (I J : CommIdeal) → I .fst ⊆ (I +i J) .fst
 +iLincl I J x x∈I = ∣ (x , 0r) , x∈I , J .snd .contains0 , sym (+Rid x) ∣

 +iRespLincl : ∀ (I J K : CommIdeal) → I .fst ⊆ J .fst → (I +i K) .fst ⊆ (J +i K) .fst
 +iRespLincl I J K I⊆J x = map λ ((y , z) , y∈I , z∈K , x≡y+z) → ((y , z) , I⊆J y y∈I , z∈K , x≡y+z)

 -- +iAssoc : ∀ (I J K : CommIdeal) → I +i (J +i K) ≡ (I +i J) +i K
 -- +iAssoc I J K = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (incl1 , incl2))
 --  where
 --  incl1 : (I +i (J +i K)) .fst ⊆ ((I +i J) +i K) .fst
 --  incl1 x = {!!}
 --  incl2 : ((I +i J) +i K) .fst ⊆ (I +i (J +i K)) .fst
 --  incl2 = {!!}

 +iIdem : ∀ (I : CommIdeal) → I +i I ≡ I
 +iIdem I = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (incl1 , incl2))
  where
  incl1 : (I +i I) .fst ⊆ I .fst
  incl1 x = rec (I .fst x .snd) λ ((y , z) , y∈I , z∈I , x≡y+z)
                                  → subst-∈ (I .fst) (sym x≡y+z) (I .snd .+Closed y∈I z∈I)

  incl2 : I .fst ⊆ (I +i I) .fst
  incl2 x x∈I = ∣ (0r , x) , I .snd .contains0 , x∈I , sym (+Lid _) ∣


 -- where to put this?
 mul++dist : ∀ {n m : ℕ} (α U : FinVec R n) (β V : FinVec R m) (j : Fin (n +ℕ m))
            → ((λ i → α i · U i) ++Fin (λ i → β i · V i)) j ≡ (α ++Fin β) j · (U ++Fin V) j
 mul++dist {n = zero} α U β V j = refl
 mul++dist {n = suc n} α U β V zero = refl
 mul++dist {n = suc n} α U β V (suc j) = mul++dist (α ∘ suc) (U ∘ suc) β V j

 -- define multiplication of ideals
 _·i_ : CommIdeal → CommIdeal → CommIdeal
 fst (I ·i J) x = (∃[ n ∈ ℕ ] Σ[ (α , β) ∈ (FinVec R n × FinVec R n) ]
                   (∀ i → α i ∈ I .fst) × (∀ i → β i ∈ J .fst) × (x ≡ ∑ λ i → α i · β i))
                    , isPropPropTrunc
 +Closed (snd (I ·i J)) = map2
  λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ) (m , (γ , δ) , ∀γi∈I , ∀δi∈J , y≡∑γδ)
   → n +ℕ m , (α ++Fin γ , β ++Fin δ) , ++FinPres∈ (I .fst) ∀αi∈I ∀γi∈I , ++FinPres∈ (J .fst) ∀βi∈J ∀δi∈J
    , cong₂ (_+_) x≡∑αβ y≡∑γδ ∙∙ sym (∑Split++ (λ i → α i · β i) (λ i → γ i · δ i)) ∙∙ ∑Ext (mul++dist α β γ δ)
 contains0 (snd (I ·i J)) = ∣ 0 , ((λ ()) , (λ ())) , (λ ()) , (λ ()) , refl ∣
 ·Closed (snd (I ·i J)) r = map
  λ (n , (α , β) , ∀αi∈I , ∀βi∈J , x≡∑αβ)
   → n , ((λ i → r · α i) , β) , (λ i → I .snd .·Closed r (∀αi∈I i)) , ∀βi∈J
    , cong (r ·_) x≡∑αβ ∙ ∑Mulrdist r (λ i → α i · β i) ∙ ∑Ext λ i → ·Assoc r (α i) (β i)
