{-# OPTIONS --cubical --safe --no-import-sorts --experimental-lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra hiding (⟨_⟩a)
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ ℓ′ : Level


-- An R-algebra is the same as a CommRing A
-- with a CommRingHomm φ : R → A
module CommAlgChar (R : CommRing {ℓ}) where
 open Iso
 open CommRingStr
 open RingHom
 open CommTheory
 open AlgebraTheory


 CommRingWithHom : Type (ℓ-suc ℓ)
 CommRingWithHom = Σ[ A ∈ CommRing {ℓ} ] CommRingHom R A

 toCommAlg : CommRingWithHom → CommAlgebra R
 CommAlgebra.Carrier (toCommAlg (A , φ)) = fst A
 CommAlgebra.0a (toCommAlg (A , φ)) = 0r (snd A)
 CommAlgebra.1a (toCommAlg (A , φ)) = 1r (snd A)
 CommAlgebra._+_ (toCommAlg (A , φ)) = _+_ (snd A)
 CommAlgebra._·_ (toCommAlg (A , φ)) = _·_ (snd A)
 CommAlgebra.- toCommAlg (A , φ) = -_ (snd A)
 CommAlgebra._⋆_ (toCommAlg (A , φ)) r a = _·_ (snd A) ((f φ) r) a --λ r a → φa · r
 CommAlgebra.isCommAlgebra (toCommAlg (A , φ)) = makeIsCommAlgebra
   (is-set (snd A))
   (+Assoc (snd A)) (+Rid (snd A)) (+Rinv (snd A)) (+Comm (snd A))
   (·Assoc (snd A)) (·Lid (snd A)) (·Ldist+ (snd A)) (·-comm (snd A))
   (λ _ _ x → cong (λ y → _·_ (snd A) y x) (isHom· φ _ _) ∙ sym (·Assoc (snd A) _ _ _))
   (λ _ _ x → cong (λ y → _·_ (snd A) y x) (isHom+ φ _ _) ∙ ·Ldist+ (snd A) _ _ _)
   (λ _ _ _ → ·Rdist+ (snd A) _ _ _)
   (λ x → cong (λ y → _·_ (snd A) y x) (pres1 φ) ∙ ·Lid (snd A) x)
   (λ _ _ _ → sym (·Assoc (snd A) _ _ _))


 fromCommAlg : CommAlgebra R → CommRingWithHom
 fst (fromCommAlg A) = CommAlgebra→CommRing A
 f (snd (fromCommAlg A)) r = CommAlgebra._⋆_ A r (CommAlgebra.1a A) -- λ r → r ⋆ 1
 pres1 (snd (fromCommAlg A)) = CommAlgebra.⋆-lid A _
 isHom+ (snd (fromCommAlg A)) _ _ = CommAlgebra.⋆-ldist A _ _ _
 isHom· (snd (fromCommAlg A)) x y =
    cong (λ a → CommAlgebra._⋆_ A (_·_ (snd R) x y) a) (sym (CommAlgebra.·Lid A _))
  ∙ ⋆Dist· (CommRing→Ring R) (CommAlgebra→Algebra A) x y (CommAlgebra.1a A) (CommAlgebra.1a A)


 CommRingWithHomRoundTrip : (Aφ : CommRingWithHom) → fromCommAlg (toCommAlg Aφ) ≡ Aφ
 CommRingWithHomRoundTrip (A , φ) = ΣPathP (APath , φPathP)
  where
  -- note that because we had to use makeIsCommAlgebra only the carrier-types
  -- and operations are definitionally equal. The proofs of the axioms might differ!
  APath : fst (fromCommAlg (toCommAlg (A , φ))) ≡ A
  fst (APath i) = fst A
  0r (snd (APath i)) = 0r (snd A)
  1r (snd (APath i)) = 1r (snd A)
  _+_ (snd (APath i)) = _+_ (snd A)
  _·_ (snd (APath i)) = _·_ (snd A)
  - snd (APath i) = -_ (snd A)
  isCommRing (snd (APath i)) = isProp→PathP (λ i → isPropIsCommRing _ _ _ _ _ )
             (isCommRing (snd (fst (fromCommAlg (toCommAlg (A , φ)))))) (isCommRing (snd A)) i

  -- this only works because fst (APath i) = fst A definitionally!
  φPathP : PathP (λ i → CommRingHom R (APath i)) (snd (fromCommAlg (toCommAlg (A , φ)))) φ
  φPathP = RingHomEqDep _ _ _ _ _ _ λ i x → ·Rid (snd A) (f φ x) i


 CommAlgRoundTrip : (A : CommAlgebra R) → toCommAlg (fromCommAlg A) ≡ A
 CommAlgebra.Carrier (CommAlgRoundTrip A i) = CommAlgebra.Carrier A
 CommAlgebra.0a (CommAlgRoundTrip A i) = CommAlgebra.0a A
 CommAlgebra.1a (CommAlgRoundTrip A i) = CommAlgebra.1a A
 CommAlgebra._+_ (CommAlgRoundTrip A i) = CommAlgebra._+_ A
 CommAlgebra._·_ (CommAlgRoundTrip A i) = CommAlgebra._·_ A
 CommAlgebra.- CommAlgRoundTrip A i = CommAlgebra.-_ A
 CommAlgebra._⋆_ (CommAlgRoundTrip A i) r x = (CommAlgebra.⋆-lassoc A r (CommAlgebra.1a A) x
                                            ∙ cong (CommAlgebra._⋆_ A r) (CommAlgebra.·Lid A x)) i
                                            -- (r ⋆ 1a) · x ≡ r ⋆ x
 CommAlgebra.isCommAlgebra (CommAlgRoundTrip A i) =
                           isProp→PathP (λ i → isPropIsCommAlgebra _ _ _ _ _
                                        (CommAlgebra._⋆_ (CommAlgRoundTrip A i)))
                                        (CommAlgebra.isCommAlgebra (toCommAlg (fromCommAlg A)))
                                        (CommAlgebra.isCommAlgebra A) i

 CommAlgIso : Iso (CommAlgebra R) CommRingWithHom
 fun CommAlgIso = fromCommAlg
 inv CommAlgIso = toCommAlg
 rightInv CommAlgIso = CommRingWithHomRoundTrip
 leftInv CommAlgIso = CommAlgRoundTrip
