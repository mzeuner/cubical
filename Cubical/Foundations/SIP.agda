{-# OPTIONS --cubical --safe #-}
module SIP  where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma.Properties

variable
 ℓ ℓ' ℓ'' : Level

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X, the pair (X , s)
-- means that X is equipped with a S-structure, wihich is witnessed by s.

⟨_⟩ : {S : Type ℓ → Type ℓ'} → Σ[ X ∈ (Type ℓ) ] (S X) → Type ℓ
⟨ X , s ⟩ = X

structure : {S : Type ℓ → Type ℓ'} (A : Σ[ X ∈ (Type ℓ) ] (S X)) → S ⟨ A ⟩
structure (X , s) = s

-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι
-- that gives us for any to types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. Moreover any sensible notion of structure should have have a proof
--    ρ (X , s) : ι (X , s) (X , s) (idEquiv X)
-- i.e. the identity function should always be a S-isomorphism. Using transport, we can prove that
-- the identity function is a S-isomorphism between (X, s) and (X , t) when s and t are identical
-- as S-structures on X:

canonical-map : {S : Type ℓ → Type ℓ'}
                (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (⟨ A ⟩ ≃ ⟨ B ⟩) → Type ℓ'')
                (ρ : (A : Σ[ X ∈ (Type ℓ) ] (S X)) → ι A A (idEquiv ⟨ A ⟩))
                {X : Type ℓ}
                (s t : S X)
                → (s ≡ t) → ι (X , s) (X , t) (idEquiv X)

canonical-map ι ρ {X} s t p = transport (λ i → ι (X , s) (X , p i) (idEquiv X)) (ρ (X , s))
--transp (λ i → ι (X , s) (X , p i) (idEquiv X)) i0 (ρ (X , s))


-- Moreover, for any good notion of structure the canonical-map should be an equivalence,
-- i.e. the witnesses in  ι (X , s) (X , t) (idEquiv X) that the identity function is a S-iso
-- should be in 1-1 correspondence with the ways to identify s and t.
-- a struture S with ι and ρ s.t. this holds is called a "standard notion of structure", or SNS.

SNS : (Type ℓ → Type ℓ') → (ℓ'' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ' (ℓ-suc ℓ'')))
SNS {ℓ} {ℓ'} S ℓ'' = Σ[ ι ∈ ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (⟨ A ⟩ ≃ ⟨ B ⟩) → Type ℓ'') ]
                    Σ[ ρ ∈ ((A : Σ[ X ∈ (Type ℓ) ] (S X)) → ι A A (idEquiv ⟨ A ⟩)) ]
                    ∀ {X : Type ℓ} (s t : S X) → isEquiv (canonical-map ι ρ s t) 


-- homomorphic means that ι has an inhabitant. (Maybe isomorphic would be more apt then)

homomorphic : {S : Type ℓ → Type ℓ'} → SNS S ℓ''
             →  ((A B : Σ[ X ∈ (Type ℓ) ] (S X)) → (⟨ A ⟩ ≃ ⟨ B ⟩) → Type ℓ'')
homomorphic (ι , ρ , θ) = ι

-- Now let S be equipped with a standard notion of structure σ and X, Y types with respective
-- S-structures s, t we want to say when (X , s) is isomorphic to (Y , t) as a (S, σ)-structure.

_≃[_]_ : {S : Type ℓ → Type ℓ'} → (Σ[ X ∈ (Type ℓ) ] (S X)) → (SNS S ℓ'')
                               → (Σ[ X ∈ (Type ℓ) ] (S X)) → (Type (ℓ-max ℓ ℓ''))
A ≃[ σ ] B = Σ[ f ∈ (⟨ A ⟩ ≃ ⟨ B ⟩) ] (homomorphic σ A B f)


-- We introduce the following function and want to show that this is an equivalence directly
-- rather than using the longish proof in the Escardo notes

Id→homEq : {S : Type ℓ → Type ℓ'} (σ : SNS S ℓ'') (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (A ≡ B) → (A ≃[ σ ] B)
Id→homEq (ι , ρ , θ) A B p = J (λ y x → A ≃[ (ι , ρ , θ) ] y) (idEquiv ⟨ A ⟩ , ρ A) p


-- transportEquiv (λ i → p i .fst) ,
--  let foo : ι A A (idEquiv ⟨ A ⟩)
--      foo = ρ A
--      goal : ι A B (transportEquiv (λ i → p i .fst))
--      goal = transport (λ i → ι A (p i) ((λ x → transp (λ j → ⟨ p (i ∧ j) ⟩ ) (~ i) x) , {!!})) foo
-- --      transport (λ j → isEquiv (λ x → transp (λ k → ⟨ p {!i!} ⟩ ) (~ i ∧ ~ j) x)) (isEquivTransport (λ k → p k .fst)))) foo
--  in goal

-- ?0 : isEquiv (λ x → transp (λ j → ⟨ p (i ∧ j) ⟩) (~ i) x),give a proof of this




-- this probably don somewhere already
Id→Eq : (X Y : Type ℓ) → (X ≡ Y) → (X ≃ Y)
Id→Eq X Y p = transport (λ i → (X ≃ p i)) (idEquiv X)
--subst (λ y → (X ≃ y)) p (idEquiv X)
--transport (λ i → (X ≃ p i)) (idEquiv X)

Id→EqRefl : (X : Type ℓ) → (Id→Eq X X refl) ≡ (idEquiv X)
Id→EqRefl X = transportRefl ((idEquiv X))



hom-lemma : {S : Type ℓ → Type ℓ'} (σ : SNS S ℓ'')
              (A B : Σ[ X ∈ (Type ℓ) ] (S X)) (p : ⟨ A ⟩ ≡ ⟨ B ⟩)
             → (subst S p (A .snd) ≡ (B .snd)) ≃ (homomorphic σ A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p))
            
hom-lemma  {S = S} (ι , ρ , θ) A B p = 
         (J (λ y x → (s : S y) → (subst S x (A .snd) ≡ s) ≃ (ι A (y , s) (Id→Eq ⟨ A ⟩ y  x)) ) δ p)
         (B. snd)
          where
             γ : (t : S ⟨ A ⟩) → ((A .snd) ≡ t) ≃ (ι A (⟨ A ⟩ , t) (idEquiv ⟨ A ⟩))
             γ t = (canonical-map ι ρ (A .snd) t , θ (A .snd) t)
             
             ε : (t : S ⟨ A ⟩) → ((A .snd) ≡ t) ≃ (ι A (⟨ A ⟩ , t) (Id→Eq ⟨ A ⟩ ⟨ A ⟩ refl))
             ε t = subst (λ f →  ((A .snd) ≡ t) ≃ (ι A (⟨ A ⟩ , t) f)) (sym (Id→EqRefl ⟨ A ⟩)) (γ t)

             δ : (t : S ⟨ A ⟩) →
                 (subst S refl (A .snd) ≡ t) ≃ ι A (⟨ A ⟩ , t) (Id→Eq ⟨ A ⟩ ⟨ A ⟩ refl)
             δ t = subst ((λ s → (s ≡ t) ≃ (ι A (⟨ A ⟩ , t) (Id→Eq ⟨ A ⟩ ⟨ A ⟩ refl))))
                   (sym (substRefl {B = S} (A .snd))) (ε t) 



-- inverse independently of SIP
Id→Eq-ua : (A B : Type ℓ) (p : A ≡ B) → (ua (Id→Eq A B p)) ≡ p
Id→Eq-ua A B p = J (λ b p → ua (Id→Eq A b p) ≡ p)
                   (subst (λ f → ua f ≡ refl) (sym (Id→EqRefl A)) uaIdEquiv) p

ua-Id→Eq : (A B : Type ℓ) (e : A ≃ B) → (Id→Eq A B (ua e)) ≡ e
ua-Id→Eq A B e = EquivJ (λ b a f →  (Id→Eq a b (ua f)) ≡ f)
                        (λ x → subst (λ r → Id→Eq x x r ≡ idEquiv x) (sym uaIdEquiv) (Id→EqRefl x))
                         B A e
               

homEq→Id : {S : Type ℓ → Type ℓ'} (σ : SNS S ℓ'') (A B : Σ[ X ∈ (Type ℓ) ] (S X))
           → (A ≃[ σ ] B) → (A ≡ B)
homEq→Id {S = S} σ A B (e , H) = sigmaPath→pathSigma A B (p , q)
                where
                 p : ⟨ A ⟩ ≡ ⟨ B ⟩
                 p = ua e
                 q : (subst S p (A .snd) ≡ (B .snd))
                 q = ((invEquiv (hom-lemma σ A B p)) .fst)
                     (subst (λ g →  homomorphic σ A B g) (sym (ua-Id→Eq ⟨ A ⟩ ⟨ B ⟩ e)) H)

-- homEq→Id' : {S : Type ℓ → Type ℓ'} (σ : SNS S ℓ'') (A B : Σ[ X ∈ (Type ℓ) ] (S X))
--            → (A ≃[ σ ] B) → (A ≡ B)
-- homEq→Id' {S = S} σ A B (e , H) i = (p i , q i)
--                 where
--                  p : ⟨ A ⟩ ≡ ⟨ B ⟩
--                  p = ua e
--                  q : PathP (λ i → S (p i)) (A .snd) (B .snd)
--                  q = {!!}




-- what Escardo uses
-- i) (σ τ : Σ X A) → (σ ≡ τ) ≃ Σ[ p ∈ (σ .fst) ≡ (τ .fst) ] (subst A p (σ .snd) ≡ (τ .snd))
-- ii) ((x : X) → A x ≃ B x) → (Σ X A ≃ Σ X B)
-- iii) (f : X ≃ Y) → Σ Y A ≃ Σ X (A ∘ f)
-- iv) (P : Σ X A → Type ℓ) → (Σ (Σ X A) P) ≃ Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))

-- Properties of the Σ-type
-- i) is pathSigma≡sigmaPath
Σ-≡-≃ : {X : Type ℓ} {A : X → Type ℓ'}
       → (σ τ : Σ X A) → ((σ ≡ τ) ≃ (Σ[ p ∈ (σ .fst) ≡ (τ .fst) ] (subst A p (σ .snd) ≡ (τ .snd))))
Σ-≡-≃ {A = A} σ τ = Id→Eq (σ ≡ τ) (Σ[ p ∈ (σ .fst) ≡ (τ .fst) ] (subst A p (σ .snd) ≡ (τ .snd)))
                 (pathSigma≡sigmaPath σ τ)

NatΣ : {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''}
      → ((x : X) → (A x) → (B x)) → (Σ X A) → (Σ X B)
NatΣ τ (x , a) = (x , τ x a)

Σ-cong : {X : Type ℓ} {A B : X → Type ℓ'} →
         ((x : X) → (A x ≡ B x)) → (Σ X A ≡ Σ X B)
Σ-cong {X = X} p i = Σ[ x ∈ X ] (p x i)


Σ-to-≡-2 : {X : Type ℓ} {A : X → Type ℓ'} {x : X} {a b : A x}
          → (a ≡ b) → PathP (λ i → Σ X A) (x , a) (x , b)
Σ-to-≡-2 {x = x} p i = (x , p i)


Σ-cong-≃ :  {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} →
         ((x : X) → (A x ≃ B x)) → (Σ X A ≃ Σ X B)
Σ-cong-≃ {X = X} {A = A} {B = B} φ = isoToEquiv (iso (NatΣ f) (NatΣ g) NatΣ-ε NatΣ-η)
 where
  f : (x : X) → (A x) → (B x)
  f x = equivFun (φ x)

  g : (x : X) → (B x) → (A x)
  g x = equivFun (invEquiv (φ x))

  η : (x : X) → (a : A x) → (g x) ((f x) a) ≡ a
  η x = retEq (invEquiv (φ x))

  ε : (x : X) → (b : B x) → f x (g x b) ≡ b
  ε x = secEq  (invEquiv (φ x))

  NatΣ-η : (w : Σ X A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a)  = (x , g x (f x a)) ≡⟨ Σ-to-≡-2 (η x a)  ⟩
                    (x , a)           ∎

  NatΣ-ε : (u : Σ X B) → NatΣ f (NatΣ g u) ≡ u
  NatΣ-ε (x , b) = (x , f x (g x b)) ≡⟨ Σ-to-≡-2 (ε x b) ⟩
                   (x , b)           ∎
  
-- Id→Eq (Σ X A) (Σ X B) (Σ-cong p)
--         where
--          p : (x : X) → (A x ≡ B x)
--          p x = ua (H x)


Σ-change-of-variable-Iso :  {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                           → (isHAEquiv f) → (Iso (Σ X (A ∘ f)) (Σ Y A))
Σ-change-of-variable-Iso {ℓ = ℓ} {ℓ' = ℓ'} {X = X} {Y = Y} {A = A} f isHAEquivf = iso φ ψ φψ ψφ
  where
   g : Y → X
   g = isHAEquiv.g isHAEquivf
   ε : (x : X) → (g (f x)) ≡ x
   ε = isHAEquiv.sec isHAEquivf
   η : (y : Y) → f (g y) ≡ y
   η = isHAEquiv.ret isHAEquivf
   τ :  (x : X) → cong f (ε x) ≡ η (f x)
   τ = isHAEquiv.com isHAEquivf
   
   φ : (Σ X (A ∘ f)) → (Σ Y A)
   φ (x , a) = (f x , a)

   ψ : (Σ Y A) → (Σ X (A ∘ f))
   ψ (y , a) = (g y , subst A (sym (η y)) a)

   φψ : (z : (Σ Y A)) → φ (ψ z) ≡ z
   φψ (y , a) = sigmaPath→pathSigma (φ (ψ (y , a))) (y , a)
                                    (η y ,  transportTransport⁻ (λ i → A (η y i)) a)
     -- last term proves transp (λ i → A (η y i)) i0 (transp (λ i → A (η y (~ i))) i0 a) ≡ a

   ψφ : (z : (Σ X (A ∘ f))) → ψ (φ z) ≡ z 
   ψφ (x , a) = sigmaPath→pathSigma (ψ (φ (x , a))) (x , a) (ε x , q)
     where
      b : A (f (g (f x)))
      b = (transp (λ i → A (η (f x) (~ i))) i0 a)
    
      q : transp (λ i → A (f (ε x i))) i0 (transp (λ i → A (η (f x) (~ i))) i0 a) ≡ a
      q =  transp (λ i → A (f (ε x i))) i0 b  ≡⟨ S ⟩
           transp (λ i → A (η (f x) i)) i0 b  ≡⟨ transportTransport⁻ (λ i → A (η (f x) i)) a ⟩
           a                                  ∎
       where
        S : (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (η (f x) i)) i0 b)
        S = subst (λ p → (transp (λ i → A (f (ε x i))) i0 b)  ≡ (transp (λ i → A (p i)) i0 b))
                 (τ x) refl

Σ-change-of-variable-≃ : {X : Type ℓ} {Y : Type ℓ'} {A : Y → Type ℓ''} (f : X → Y)
                      → (isEquiv f) → ((Σ X (A ∘ f)) ≃ (Σ Y A))
Σ-change-of-variable-≃ f isEquivf =
                      isoToEquiv (Σ-change-of-variable-Iso f (equiv→HAEquiv (f , isEquivf) .snd))

                    -- EquivJ P d
                    -- Y X ((f ,  isEquivf)) A
                    --   where
                    --    P : (Y X : Type ℓ) (f : X ≃ Y) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
                    --    P Y X f = (A : Y → Type ℓ') → ((Σ X (A ∘ (f .fst))) ≃ (Σ Y A))

                    --    d : (X : Type ℓ) → P X X (idEquiv X)
                    --    d X A = idEquiv (Σ X A)



Σ-assoc-Iso : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Iso (Σ (Σ X A) P) (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))))
Σ-assoc-Iso X A P = iso f g ε η
   where
    f : (Σ (Σ X A) P) → (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
    f ((x , a) , p) = (x , (a , p))
    g : (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a))) →  (Σ (Σ X A) P)
    g (x , (a , p)) = ((x , a) , p)
    ε : section f g
    ε n = refl
    η : retract f g
    η m = refl

Σ-assoc-≃ : (X : Type ℓ) (A : X → Type ℓ') (P : Σ X A → Type ℓ'')
         → (Σ (Σ X A) P) ≃ (Σ[ x ∈ X ] (Σ[ a ∈ A x ] P (x , a)))
Σ-assoc-≃ X A P = isoToEquiv (Σ-assoc-Iso X A P)


-- SIP 
_≃⟨_⟩_ : (X : Type ℓ) {Y : Type ℓ'} {Z : Type ℓ''} → (X ≃ Y) → (Y ≃ Z) → (X ≃ Z)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (X : Type ℓ) → (X ≃ X)
_■ = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

SIP :  {S : Type ℓ → Type ℓ'} (σ : SNS S ℓ'')
       (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → ((A ≡ B) ≃ (A ≃[ σ ] B))
SIP {ℓ} {ℓ'} {ℓ''} {S = S} σ A B =
            (A ≡ B)                                                  ≃⟨ i ⟩
            (Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ] (subst S p (A .snd) ≡ (B .snd))) ≃⟨ ii ⟩
            (Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ] (ι A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p)))   ≃⟨ iii ⟩
            (A ≃[ σ ] B)                                             ■
              where
               ι = homomorphic σ
             
               i =   Σ-≡-≃ {ℓ = ℓ-suc ℓ} {X = Type ℓ} A B
               ii =  Σ-cong-≃ (hom-lemma σ A B)
               iii = Σ-change-of-variable-≃ (Id→Eq ⟨ A ⟩ ⟨ B ⟩)
                    (isoToEquiv
                     (iso (Id→Eq ⟨ A ⟩ ⟨ B ⟩) ua (ua-Id→Eq ⟨ A ⟩ ⟨ B ⟩) (Id→Eq-ua ⟨ A ⟩ ⟨ B ⟩)) .snd) 





-- more lemmas
equivs-closed-under-∼ : {X : Type ℓ} {Y : Type ℓ'} {f g : X → Y} →
                       ((x : X) → (f x) ≡ (g x)) → (isEquiv f) → (isEquiv g)
equivs-closed-under-∼ H equivf = transport (λ i → isEquiv ((funExt H) i)) equivf


transp-lemma : {X : Type ℓ} (x y : X) (p : x ≡ y)
              → transp (λ i → x ≡ p i) i0 (λ _ → x) ≡ p
transp-lemma {ℓ = ℓ} {X = X} x y p = goal
 where
  bar : PathP (λ k → x ≡ y)
              (\ j → comp (λ _ → X) (λ i → \ { (j = i0) → x ; (j = i1) → p i }) x)
              (\ j → hcomp (λ i → \ { (j = i0) → x ; (j = i1) → p i }) x)
  bar k j = comp (λ _ → X) (λ i → \ { (j = i0) → x ; (j = i1) → p i
                                    ; (k = i1) → hfill (λ i → λ { (j = i0) → x ; (j = i1) → p i }) (inS x) i}) x

  baz : refl ∙ p ≡ p
  baz = sym (lUnit p)

  goal : (λ j → comp (λ _ → X) (λ i → \ { (j = i0) → x ; (j = i1) → p i }) x) ≡ p
  goal = bar ∙ baz





-- Pointed types

pointed-type-structure : Type ℓ → Type ℓ
pointed-type-structure X = X

Pointed-Type : Type (ℓ-suc ℓ)
Pointed-Type {ℓ = ℓ} = Σ (Type ℓ) pointed-type-structure

pointed-is-sns : SNS pointed-type-structure ℓ
pointed-is-sns {ℓ = ℓ} = (ι , ρ , θ)
  where
   ι : (A B : Pointed-Type) → (⟨ A ⟩ ≃ ⟨ B ⟩) → Type ℓ
   ι (X , x) (Y , y) f = (f .fst) x ≡ y

   ρ : (A : Pointed-Type) → ι A A (idEquiv ⟨ A ⟩)
   ρ (X , x) = refl

   θ : {X : Type ℓ} (x y : pointed-type-structure X) → isEquiv (canonical-map ι ρ x y)
   θ x y = equivs-closed-under-∼ H (idIsEquiv (x ≡ y))
     where
      H : (p : x ≡ y) → p  ≡  (canonical-map ι ρ x y p)
      H p = sym (transp-lemma x y p)
-- need: transp (λ i → x ≡ p i) i0 (λ _ → x) ≡ p


pointed-type-to-≡ : (X Y : Type ℓ) (x : X) (y : Y) (f : (X ≃ Y))
                   → ((f .fst) x ≡ y) → (X , x) ≡ (Y , y)
pointed-type-to-≡ X Y x y f p = homEq→Id pointed-is-sns (X , x) (Y , y) ((f , p))

pointed-type-sip : (X Y : Type ℓ) (x : X) (y : Y)
                   → ((Σ[ f ∈ X ≃ Y ] (f .fst) x ≡ y) ≃ ((X , x) ≡ (Y , y)))
pointed-type-sip X Y x y = invEquiv (SIP pointed-is-sns (X , x) (Y , y)) 



-- -- Type embeddings
-- module _ (X : Type ℓ) where

--  is-embedding : {Y : Type ℓ'} (f : Y → X) → Type (ℓ-max ℓ ℓ')
--  is-embedding {Y = Y} f = (y : Y) → isContr (fiber f (f y))
              
--  Subtypes-structure : Type ℓ' → Type (ℓ-max ℓ ℓ')
--  Subtypes-structure Y = Σ[ f ∈ (Y → X) ](is-embedding f)

--  Subtype : Type (ℓ-max ℓ (ℓ-suc ℓ'))
--  Subtype {ℓ' = ℓ'} = Σ (Type ℓ') Subtypes-structure

--  subtypes-is-sns : SNS {ℓ = ℓ'} Subtypes-structure (ℓ-max ℓ ℓ')
--  subtypes-is-sns  = (ι , {!!}  , {!!})
--   where
--    ι : (A B : Subtype)  → (⟨ A ⟩ ≃ ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')    
--    ι A B f = (a : ⟨ A ⟩) → (structure A .fst) a ≡ (structure B .fst) ((f .fst) a)
