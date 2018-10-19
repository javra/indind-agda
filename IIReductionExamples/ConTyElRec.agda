{-# OPTIONS --rewriting #-}

module IIReductionExamples.ConTyElRec where

open import StrictLib renaming (_Σ,_ to _,_)

-- Prop trunc
--------------------------------------------------------------------------------

-- postulate
--   ∣_∣   : ∀ {α} → Set α → Set α
--   emb   : ∀ {α}{A : Set α} → A → ∣ A ∣
--   trunc : ∀ {α}{A : Set α}(x y : ∣ A ∣) → x ≡ y
--   ∣∣-rec :
--     ∀ {α β}{A : Set α}{P : Set β}
--     → (A → P) → ((x y : P) → x ≡ y) → ∣ A ∣ → P
--   ∣∣-rec-emb :
--     ∀ {α β A P embedᴾ truncᴾ a}
--     → ∣∣-rec {α}{β}{A}{P} embedᴾ truncᴾ (emb a) ≡ embedᴾ a
-- {-# REWRITE ∣∣-rec-emb #-}


-- Quotients
--------------------------------------------------------------------------------

module _ {α β : Level} where
  postulate
    _/_  : (A : Set α)(R : A → A → Set β) → Set (α ⊔ β)
    emb  : ∀ {A R} → A → A / R
    quot : ∀{A R}{x y : A} → R x y → emb {A}{R} x ≡ emb y
    /rec : ∀ {γ}{A R}{P : Set γ}
             (embᴿ : A → P)
             (quotᴿ : ∀ {x y} → R x y → embᴿ x ≡ embᴿ y)
           → A / R → P
    embβ : ∀ {A : Set α}{R : A → A → Set β}{P : Set α}
             (embᴿ : A → P)
             (quotᴿ : ∀ {x y} → R x y → embᴿ x ≡ embᴿ y)
           → ∀ x → /rec embᴿ quotᴿ (emb x) ≡ embᴿ x
{-# REWRITE embβ #-}

-- Intrinsic
--------------------------------------------------------------------------------

record ConTy {ℓ} : Set (suc ℓ) where
  infixl 5 _▶_
  field
    Con  : Set ℓ
    Ty   : Con → Set ℓ
    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con
    U    : (Γ : Con) → Ty Γ
    Sg   : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ
    El   : (Γ : Con) → Ty (Γ ▶ U Γ)
    ▶Sg  : ∀ {Γ A B} → (Γ ▶ Sg Γ A B) ≡ (Γ ▶ A ▶ B)

record ConTyᴿ {ℓ₁}{ℓ₂}(M : ConTy {ℓ₁})(N : ConTy {ℓ₂}) : Set (ℓ₁ ⊔ ℓ₂) where
  private module M = ConTy M
  private module N = ConTy N
  field
    Con : M.Con → N.Con
    Ty  : ∀{Γ} → M.Ty Γ → N.Ty (Con Γ)
    •   : Con M.∙ ≡ N.∙
    ▶   : ∀{Γ A} → Con (Γ M.▶ A) ≡ Con Γ N.▶ Ty A
    U   : ∀{Γ} → Ty (M.U Γ) ≡ N.U (Con Γ)
    Sg  : ∀{Γ A B} → Ty (M.Sg Γ A B) ≡ N.Sg (Con Γ) (Ty A) (tr N.Ty ▶ (Ty B))
    El  : ∀{Γ} → tr N.Ty (▶ ◾ ap (Con Γ N.▶_) U) (Ty (M.El Γ)) ≡ (N.El (Con Γ))

--------------------------------------------------------------------------------

-- infixl 6 _▶_

-- data P : Set where
--   ∙   : P
--   _▶_ : P → P → P
--   U   : P → P
--   Sg  : P → P → P → P
--   El  : P → P

-- P' = P / (λ t u → ∃₂ λ Γ A → ∃ λ B → (t ≡ Γ ▶ Sg Γ A B) × (u ≡ Γ ▶ A ▶ B))

-- Conw : P → Set
-- Tyw  : P → P → Set
-- Conw ∙          = ⊤
-- Conw (Γ ▶ A)    = Conw Γ × Tyw Γ A
-- Conw (U _)      = ⊥
-- Conw (Sg _ _ _) = ⊥
-- Conw (El _)     = ⊥
-- Tyw Γ ∙          = ⊥
-- Tyw Γ (_ ▶ _)    = ⊥
-- Tyw Γ (U Δ)      = Conw Δ × (Δ ≡ Γ)
-- Tyw Γ (Sg Δ A B) = Conw Δ × Tyw Δ A × Tyw (Δ ▶ A) B × (Δ ≡ Γ)
-- Tyw Γ (El Δ)     = Conw Δ × ((Δ ▶ (U Δ)) ≡ Γ)

-- prop : ∀ {α}(A : Set α) → Set α
-- prop A = (x y : A) → x ≡ y

-- ConwProp : ∀ Γ → prop (Conw Γ)
-- TywProp  : ∀ Γ A → prop (Tyw Γ A)
-- ConwProp ∙          = λ _ _ → refl
-- ConwProp (Γ ▶ A)    = λ {(Γw , Aw)(Γw' , Aw') →
--                           ap _,_ (ConwProp Γ Γw Γw') ⊗ TywProp Γ A Aw Aw'}
-- ConwProp (U _)      = λ ()
-- ConwProp (Sg _ _ _) = λ ()
-- ConwProp (El _)     = λ ()
-- TywProp Γ ∙ = λ ()
-- TywProp Γ (_ ▶ _) = λ ()
-- TywProp Γ (U Δ)      = λ {(Δw , refl) (Δw' , refl) → ap (_, refl) (ConwProp Γ Δw Δw')}
-- TywProp Γ (Sg Δ A B) = {!!} -- etc
-- TywProp Γ (El Δ)     = {!!} -- etc

-- postulate
--   propExt : ∀ {α}{A B : Set α} → prop A → prop B → (A → B) → (B → A) → A ≡ B

-- Conw' : P' → Set
-- Conw' = /rec Conw {!!}

-- ConTySyn : ConTy {zero}
-- ConTySyn = record
--   { Con = Σ P' (/rec Conw {!!})
--   ; Ty  = λ {(Γ , Γw) → Σ P' (/rec {!!} {!!})}
--   ; ∙   = {!!}
--   ; _▶_ = {!!}
--   ; U   = {!!}
--   ; Sg  = {!!}
--   ; El  = {!!}
--   ; ▶Sg = {!!}
--   }


infixl 6 _▶_

data Con : Set
data Ty  : Set

data Con where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Ty where
  U  : Con → Ty
  Sg : Con → Ty → Ty → Ty
  El : Con → Ty

--------------------------------------------------------------------------------

infix 6 _~⁻¹
infixr 5 _~◾_

-- data Ty~ : Con → Ty → Con → Ty → Set
-- data Con~ : Con → Con → Set

-- data Ty~ where
--   ~refl : ∀ {Γ A} → Ty~ Γ A Γ A
--   _~⁻¹  : ∀ {Γ₀ A Γ₁ B} → Ty~ Γ₀ A Γ₁ B → Ty~ Γ₁ B Γ₀ A
--   _~◾_  : ∀ {Γ₀ Γ₁ Γ₂ A B C} → Ty~ Γ₀ A Γ₁ B → Ty~ Γ₁ B Γ₂ C → Ty~ Γ₀ A Γ₂ C
--   U     : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Ty~ Γ₀ (U Γ₀) Γ₁ (U Γ₁)
--   El    : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Ty~ (Γ₀ ▶ U Γ₀) (El Γ₀) (Γ₁ ▶ U Γ₁) (El Γ₁)
--   Sg    : ∀ {Γ₀ Γ₁ A₀ A₁ B₀ B₁}
--             → Con~ Γ₀ Γ₁ → Ty~ Γ₀ A₀ Γ₁ A₁ → Ty~ (Γ₀ ▶ A₀) B₀ (Γ₁ ▶ A₁) B₁
--             → Ty~ Γ₀ (Sg Γ₀ A₀ B₀) Γ₁ (Sg Γ₁ A₁ B₁)

data Ty~ : Con → Ty → Ty → Set
data Con~ : Con → Con → Set

data Ty~ where
  ~refl : ∀ {Γ A} → Ty~ Γ A A
  _~⁻¹  : ∀ {Γ A B} → Ty~ Γ A B → Ty~ Γ B A
  _~◾_  : ∀ {Γ A B C} → Ty~ Γ A B → Ty~ Γ B C → Ty~ Γ A C
  U     : ∀ {Γ Γ'} → Con~ Γ Γ' → Ty~ Γ (U Γ) (U Γ')
  El    : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Ty~ (Γ₀ ▶ U Γ₀) (El Γ₀) (El Γ₁)
  Sg    : ∀ {Γ₀ Γ₁ A₀ A₁ B₀ B₁}
            → Con~ Γ₀ Γ₁ → Ty~ Γ₀ A₀ A₁ → Ty~ (Γ₀ ▶ A₀) B₀ B₁
            → Ty~ Γ₀ (Sg Γ₀ A₀ B₀) (Sg Γ₁ A₁ B₁)


data Con~ where
  β     : ∀ {Γ A B} → Con~ (Γ ▶ Sg Γ A B) (Γ ▶ A ▶ B)
  ~refl : ∀ {Γ} → Con~ Γ Γ
  _~⁻¹  : ∀ {Γ Δ} → Con~ Γ Δ → Con~ Δ Γ
  _~◾_  : ∀ {Γ Δ Ξ} → Con~ Γ Δ → Con~ Δ Ξ → Con~ Γ Ξ
  _▶_   : ∀ {Γ₀ Γ₁ A₀ A₁} → Con~ Γ₀ Γ₁ → Ty~ Γ₀ A₀ A₁ → Con~ (Γ₀ ▶ A₀) (Γ₁ ▶ A₁)

data Conw : Con → Set
data Tyw  : Con → Ty → Set

data Conw where
  ∙w : Conw ∙
  ▶w : ∀ {Γ A} → Conw Γ → Tyw Γ A → Conw (Γ ▶ A)

data Tyw where
  Uw  : ∀ {Γ} → Conw Γ → Tyw Γ (U Γ)
  Elw : ∀ {Γ} → Conw Γ → Tyw (Γ ▶ U Γ) (El Γ)
  Sgw : ∀ {Γ A B} → Conw Γ → Tyw Γ A → Tyw (Γ ▶ A) B → Tyw Γ (Sg Γ A B)
  coeTy : ∀ {Γ₀ Γ₁ A} → Con~ Γ₀ Γ₁ → Tyw Γ₀ A → Tyw Γ₁ A

lem : ∀ {Γ Γ'} → Con~ Γ Γ' → (Conw Γ → Conw Γ') × (Conw Γ' → Conw Γ)
lem p = {!!}

-- Syntax
--------------------------------------------------------------------------------

∣_∣ : ∀ {α}(A : Set α) → Set α
∣ A ∣ = A / (λ _ _ → ⊤)

prop : ∀ {α}(A : Set α) → Set α
prop A = (x y : A) → x ≡ y

postulate
  Con~≡ : ∀ {Γ Γ'} → Con~ Γ Γ' → Conw Γ ≡ Conw Γ'
  Ty~≡ : ∀ {A A' Γ} → Ty~ Γ A A' → Tyw Γ A ≡ Tyw Γ A'

postulate
  propExt : ∀ {α}{A B : Set α} → prop A → prop B → (A → B) → (B → A) → A ≡ B

ConTySyn : ConTy {zero}
ConTySyn = record
  { Con = Σ (Con / Con~) (/rec Conw Con~≡)
  ; Ty  = λ {(Γ , _) → /rec (λ Γ → Σ (Ty / Ty~ Γ) (/rec (Tyw Γ) Ty~≡)) {!!} Γ}
  ; ∙   = {!!}
  ; _▶_ = {!!}
  ; U   = {!!}
  ; Sg  = {!!}
  ; El  = {!!}
  ; ▶Sg = {!!}
  }

-- ConTySyn : ConTy {zero}
-- ConTySyn = record
--   { Con = (Σ Con λ Γ → Conw Γ) / λ {(Γ , _)(Γ' , _) → ∣ Con~ Γ Γ' ∣}
--   ; Ty  = λ Γ → /rec (λ {(Γ , _) → Σ Ty (Tyw Γ) / λ {(A , _)(A' , _)
--                                  → ∣ Ty~ Γ A A' ∣ }})
--                      (λ { {Γ , _}{Γ' , _} p → {!!}})
--                      Γ
--   ; ∙   = {!!}
--   ; _▶_ = {!!}
--   ; U   = {!!}
--   ; Sg  = {!!}
--   ; El  = {!!}
--   ; ▶Sg = {!!}
--   }
