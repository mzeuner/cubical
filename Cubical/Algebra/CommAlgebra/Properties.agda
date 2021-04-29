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
 CommRingWithHomRoundTrip (A , φ) = ΣPathP
                          (equivFun (CommRingPath _ _) (idEquiv (A .fst) , idEquivIsRingEquiv)
                          , foo)
  where
  -- note that because we had to use makeIsCommAlgebra only the carrier-types
  -- and operations are definitionally equal. The proofs of the axioms might differ!
  idEquivIsRingEquiv : CommRingEquiv (fromCommAlg (toCommAlg (A , φ)) .fst) A (idEquiv  (A .fst))
  RingEquiv.pres1 idEquivIsRingEquiv = refl
  RingEquiv.isHom+ idEquivIsRingEquiv x y = refl
  RingEquiv.isHom· idEquivIsRingEquiv x y = refl

  -- bar : PathP (λ i → (R .fst) → (A .fst)) (fromCommAlg (toCommAlg (A , φ)) .snd .f) (φ .f)
  -- bar = funExt (λ x → ·Rid (snd A) (φ .f x))

  baz : PathP (λ i → (R .fst) →
              (equivFun (CommRingPath (fromCommAlg (toCommAlg (A , φ)) .fst) A) (idEquiv (A .fst)
              , idEquivIsRingEquiv) i) .fst)
              (fromCommAlg (toCommAlg (A , φ)) .snd .f) (φ .f)
  baz = funExt bar
   where
   bar : (x : R .fst) → PathP (λ i →
                               equivFun (CommRingPath (fromCommAlg (toCommAlg (A , φ)) .fst) A)
                               (idEquiv (A .fst) , idEquivIsRingEquiv) i .fst)
         (fromCommAlg (toCommAlg (A , φ)) .snd .f x) (φ .f x)
   bar x = toPathP {!!}
  -- baz i x = ·Rid ((equivFun (CommRingPath (fromCommAlg (toCommAlg (A , φ)) .fst) A)
  --                 (idEquiv (A .fst)
  --             , idEquivIsRingEquiv) i) .snd) {!!} i
  -- (toPathP (transportRefl (f φ x)) i)


  foo : PathP (λ i → CommRingHom R
              (equivFun (CommRingPath (fromCommAlg (toCommAlg (A , φ)) .fst) A) (idEquiv (A .fst)
              , idEquivIsRingEquiv) i))
              (fromCommAlg (toCommAlg (A , φ)) .snd) φ
  foo = RingHomEqDep _ _ _ _ _ _ baz --doesn't accept bar
