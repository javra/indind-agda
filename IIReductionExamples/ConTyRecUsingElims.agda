{-# OPTIONS --without-K --rewriting #-}

{-
  Constructing the recursor (without uniqueness so far) for ConTy
  inductive-inductive example. No UIP, funext, propext, quotients or
  recursion-recursion are used.

  This version uses postulated eliminator for the presyntax.
  It takes a rather long time to typecheck.
-}

module IIReductionExamples.ConTyRecUsingElims where

open import Lib

-- Intrinsic models
--------------------------------------------------------------------------------

-- Models
record ConTy {ℓ} : Set (suc ℓ) where
  infixl 5 _▶_
  field
    Con  : Set ℓ
    Ty   : Con → Set ℓ
    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con
    U    : (Γ : Con) → Ty Γ
    Π    : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ

-- Morphisms
record ConTyᴿ {ℓ₁}{ℓ₂}(M : ConTy {ℓ₁})(N : ConTy {ℓ₂}) : Set (ℓ₁ ⊔ ℓ₂) where
  private module M = ConTy M
  private module N = ConTy N
  field
    Con : M.Con → N.Con
    Ty  : ∀{Γ} → M.Ty Γ → N.Ty (Con Γ)
    •   : Con M.∙ ≡ N.∙
    ▶   : ∀{Γ A} → Con (Γ M.▶ A) ≡ Con Γ N.▶ Ty A
    U   : ∀{Γ} → Ty (M.U Γ) ≡ N.U (Con Γ)
    Π   : ∀{Γ A B} → Ty (M.Π Γ A B) ≡ N.Π (Con Γ) (Ty A) (tr N.Ty ▶ (Ty B))

-- Premodels
--------------------------------------------------------------------------------

-- Models
record ConTyᴾ {ℓ} : Set (suc ℓ) where
  infixl 5 _▶_
  field
    Con : Set ℓ
    Ty  : Set ℓ
    ∙   : Con
    _▶_ : Con → Ty → Con
    U   : Con → Ty
    Π   : Con → Ty → Ty → Ty

-- Dependent models
record ConTyᴾᴹ {α β}(C : ConTyᴾ {α}) : Set (α ⊔ suc β) where
  private module C = ConTyᴾ C
  infixl 5 _▶_
  field
    Con  : C.Con → Set β
    Ty   : C.Ty  → Set β
    ∙    : Con C.∙
    _▶_  : ∀ {Γ} (Γᴹ : Con Γ){A}(Aᴹ : Ty A) → Con (Γ C.▶ A)
    U    : ∀ {Γ}(Γᴹ : Con Γ) → Ty (C.U Γ)
    Π    : ∀ {Γ} (Γᴹ : Con Γ){A}(Aᴹ : Ty A){B}(Bᴹ : Ty B) → Ty (C.Π Γ A B)

-- Eliminators
record ConTyᴾᴱ {α β}(C : ConTyᴾ {α})(M : ConTyᴾᴹ {α}{β} C) : Set (α ⊔ β) where
  private module C = ConTyᴾ C
  private module M = ConTyᴾᴹ M
  field
    Con : ∀ Γ → M.Con Γ
    Ty  : ∀ A → M.Ty A
    ∙   : Con C.∙ ≡ M.∙
    ▶   : ∀ {Γ A} → Con (Γ C.▶ A) ≡ Con Γ M.▶ Ty A
    U   : ∀ {Γ} → Ty (C.U Γ) ≡ M.U (Con Γ)
    Π   : ∀ {Γ A B} → Ty (C.Π Γ A B) ≡ M.Π (Con Γ) (Ty A) (Ty B)

-- Presyntax declaration
postulate ConTyᴾSyn : ConTyᴾ {zero}
module P = ConTyᴾ ConTyᴾSyn

-- Presyntax induction declaration
module _ {β}(M : ConTyᴾᴹ {β = β} ConTyᴾSyn) where
  postulate ConTyᴾElim : ConTyᴾᴱ _ M
  open ConTyᴾᴱ ConTyᴾElim
  {-# REWRITE ∙ ▶ U Π #-}

-- Well-formedness predicates
--------------------------------------------------------------------------------

-- (It is easy to show that w is propositional, but we don't actually
--  need that proof here)
module W = ConTyᴾᴱ (ConTyᴾElim record
  { Con = λ _ → Set
  ; Ty  = λ _ → P.Con → Set
  ; ∙   = ⊤
  ; _▶_ = λ {Γ} Γᴹ {A} Aᴹ → Γᴹ × Aᴹ Γ
  ; U   = λ {Γ} Γᴹ Δ → Δ ≡ Γ
  ; Π   = λ {Γ} Γᴹ {A} Aᴹ {B} Bᴹ Δ → (Δ ≡ Γ) × Aᴹ Δ × Bᴹ (Γ P.▶ A)
  })

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

ConTySyn : ConTy {zero}
ConTySyn = record
  { Con = ∃ W.Con
  ; Ty  = λ {(Γ , _) → Σ P.Ty λ A → W.Ty A Γ}
  ; ∙   = P.∙ , tt
  ; _▶_ = λ {(Γ , Γw) (A , Aw) → (Γ P.▶ A) , Γw , Aw}
  ; U   = λ {(Γ , Γw) → P.U Γ , refl}
  ; Π   = λ {(Γ , Γw)(A , Aw)(B , Bw) → P.Π Γ A B , refl , Aw , Bw}}

module Syn = ConTy ConTySyn

-- Recursion for inductive-inductive syntax
--------------------------------------------------------------------------------

module _ {α}(M : ConTy {α}) where
  module M = ConTy M

  -- Logical relation between the presyntax and the M model expressing
  -- that presyntactic and semantic values have the same structure
  module ~ = ConTyᴾᴱ (ConTyᴾElim (record
    { Con = λ Γ → M.Con → Set α
    ; Ty  = λ A → ∀ γ → M.Ty γ → Set α
    ; ∙   = λ γ → γ ≡ M.∙
    ; _▶_ = λ Γ~ A~ γ → ∃₂ λ γ₀ α → Γ~ γ₀ × A~ γ₀ α × (γ ≡ γ₀ M.▶ α)
    ; U   = λ Γ~ γ α → Γ~ γ × (α ≡ M.U γ)
    ; Π   = λ Γ~ A~ B~ γ α → Γ~ γ × (∃₂ λ α₀ α₁ → A~ γ α₀ × B~ (γ M.▶ α₀) α₁ × (α ≡ M.Π γ α₀ α₁))
    }))

  -- Semantic values with the same presyntactic structure are equal
  ~≡Con : P.Con → Set α
  ~≡Con Γ = ∀ γ γ' → ~.Con Γ γ  → ~.Con Γ γ' → γ ≡ γ'

  ~≡Ty : P.Ty → Set α
  ~≡Ty A = ∀ γ α α' → ~.Ty A γ α → ~.Ty A γ α' → α ≡ α'

  ~≡∙ : ~≡Con P.∙
  ~≡∙ γ γ' p q = p ◾ q ⁻¹

  ~≡▶ : ∀ {Γ} → ~≡Con Γ → ∀ {A} → ~≡Ty A → ~≡Con (Γ P.▶ A)
  ~≡▶ Γᴹ Aᴹ  _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl)
    with Γᴹ γ γ' ~γ ~γ'
  ... | refl = _&_ (γ' M.▶_) (Aᴹ γ α α' ~α ~α')

  ~≡U : ∀ {Γ} → ~≡Con Γ → ~≡Ty (P.U Γ)
  ~≡U Δᴹ γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹

  ~≡Π : ∀ {Γ} → ~≡Con Γ → ∀ {A} → ~≡Ty A → ∀ {B} → ~≡Ty B → ~≡Ty (P.Π Γ A B)
  ~≡Π Γᴹ Aᴹ Bᴹ γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
                     (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl)
                     with Aᴹ γ α₀ α₀' ~α₀ ~α₀'
  ... | refl = _&_ (M.Π γ α₀') (Bᴹ (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

  module ~≡ = ConTyᴾᴱ (ConTyᴾElim (record
    { Con = ~≡Con
    ; Ty  = ~≡Ty
    ; ∙   = ~≡∙
    ; _▶_ = λ {Γ} → ~≡▶ {Γ}
    ; U   = λ {Γ} → ~≡U {Γ}
    ; Π   = λ {Γ} → ~≡Π {Γ}
    }))

  -- ... which equality is refl in the degenerate case
  ~reflCon : P.Con → Set α
  ~reflCon Γ = ∀ γ ~γ → ~≡.Con Γ γ γ ~γ ~γ ≡ refl

  ~reflTy : P.Ty → Set α
  ~reflTy A = ∀ γ α ~α → ~≡.Ty A γ α α ~α ~α ≡ refl

  ~refl∙ : ~reflCon P.∙
  ~refl∙ Γ refl = refl

  ~refl▶ : ∀ {Γ}(Γᴹ : ~reflCon Γ){A}(Aᴹ : ~reflTy A) → ~reflCon (Γ P.▶ A)
  ~refl▶ Γᴹ Aᴹ _ (γ , α , ~γ , ~α , refl) rewrite Γᴹ γ ~γ | Aᴹ γ α ~α = refl

  ~reflU : ∀ {Γ} → ~reflCon Γ → ~reflTy (P.U Γ)
  ~reflU Γᴹ γ _ (~γ , refl) = refl

  ~reflΠ : ∀ {Γ}(Γᴹ : ~reflCon Γ) {A} (Aᴹ : ~reflTy A){B}(Bᴹ : ~reflTy B) → ~reflTy (P.Π Γ A B)
  ~reflΠ Γᴹ Aᴹ Bᴹ γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
    rewrite Aᴹ γ α₀ ~α₀ | Bᴹ (γ M.▶ α₀) α₁ ~α₁ = refl

  module ~refl = ConTyᴾᴱ (ConTyᴾElim (record
    { Con = ~reflCon
    ; Ty  = ~reflTy
    ; ∙   = ~refl∙
    ; _▶_ = λ {Γ} → ~refl▶ {Γ}
    ; U   = λ {Γ} → ~reflU {Γ}
    ; Π   = λ {Γ} → ~reflΠ {Γ}
    }))

  -- Interpretation of the well-formed presyntax in M.
  -- We have redundant ~ witnesses, but we must always return the topmost ones,
  -- which is the canonical choice, in order to avoid UIP for recursion.
  ⟦⟧Con : P.Con → Set α
  ⟦⟧Con Γ = W.Con Γ → ∃ λ γ → ~.Con Γ γ

  ⟦⟧Ty : P.Ty → Set α
  ⟦⟧Ty A = ∀ Γ → W.Con Γ → W.Ty A Γ → ∃₂ λ γ α → ~.Con Γ γ × ~.Ty A γ α

  ⟦⟧∙ : ⟦⟧Con P.∙
  ⟦⟧∙ _ = M.∙ , refl

  ⟦⟧▶ : ∀ {Γ} → ⟦⟧Con Γ → ∀ {A} → ⟦⟧Ty A → ⟦⟧Con (Γ P.▶ A)
  ⟦⟧▶ {Γ} Γᴹ Aᴹ (Γw , Aw) with Γᴹ Γw | Aᴹ Γ Γw Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with ~≡.Con Γ γ γ' ~γ ~γ'
  ... | refl = (γ M.▶ α) , (γ , α , ~γ , ~α , refl)

  ⟦⟧U : ∀ {Γ} → ⟦⟧Con Γ → ⟦⟧Ty (P.U Γ)
  ⟦⟧U Γᴹ _ Γw refl with Γᴹ Γw
  ... | (γ , ~γ) = γ , M.U γ , ~γ , ~γ , refl

  ⟦⟧Π : ∀ {Γ} → ⟦⟧Con Γ → ∀ {A} → ⟦⟧Ty A → ∀ {B} → ⟦⟧Ty B → ⟦⟧Ty (P.Π Γ A B)
  ⟦⟧Π {Γ} Γᴹ {A} Aᴹ Bᴹ _ Γw (refl , Aw , Bw) with Γᴹ Γw | Aᴹ Γ Γw Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with ~≡.Con Γ γ γ' ~γ ~γ'
  ... | refl with Bᴹ (Γ P.▶ A) (Γw , Aw) Bw
  ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with ~≡.Con Γ γ γ'' ~γ ~γ''
  ... | refl with ~≡.Ty A γ'' α α' ~α ~α'
  ... | refl = γ , M.Π γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

  module ⟦⟧ = ConTyᴾᴱ (ConTyᴾElim (record
    { Con = ⟦⟧Con
    ; Ty  = ⟦⟧Ty
    ; ∙   = ⟦⟧∙
    ; _▶_ = λ {Γ} → ⟦⟧▶ {Γ}
    ; U   = λ {Γ} → ⟦⟧U {Γ}
    ; Π   = λ {Γ} → ⟦⟧Π {Γ} }))

  -- Recursion
  Conᴿ : Syn.Con → M.Con
  Conᴿ (Γ , Γw) = ₁ (⟦⟧.Con Γ Γw)

  Tyᴿ : ∀ {Γ} → Syn.Ty Γ → M.Ty (Conᴿ Γ)
  Tyᴿ {Γ , Γw} (A , Aw) with ⟦⟧.Con Γ Γw | ⟦⟧.Ty A Γ Γw Aw
  ... | γ , ~γ | γ' , α , ~γ' , ~α with ~≡.Con Γ γ γ' ~γ ~γ'
  ... | refl = α

  ▶ᴿ : ∀ {Γ A} → Conᴿ (Γ Syn.▶ A) ≡ Conᴿ Γ M.▶ Tyᴿ A
  ▶ᴿ {Γ , Γw}{A , Aw} with ⟦⟧.Con Γ Γw | ⟦⟧.Ty A Γ Γw Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with ~≡.Con Γ γ γ' ~γ ~γ'
  ... | refl = refl

  Uᴿ : ∀ {Γ} → Tyᴿ (Syn.U Γ) ≡ M.U (Conᴿ Γ)
  Uᴿ {Γ , Γw} with ⟦⟧.Con Γ Γw
  ... | γ , ~γ rewrite ~refl.Con Γ γ ~γ = refl

  Πᴿ : ∀ {Γ A B} → Tyᴿ (Syn.Π Γ A B) ≡ M.Π (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
  Πᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦⟧.Con Γ Γw | ⟦⟧.Ty A Γ Γw Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with ~≡.Con Γ γ γ' ~γ ~γ'
  ... | refl with ⟦⟧.Ty B (Γ P.▶ A) (Γw , Aw) Bw
  ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with ~≡.Con Γ γ γ'' ~γ ~γ''
  ... | refl with ~≡.Ty A γ'' α α' ~α ~α'
  ... | refl rewrite ~refl.Con Γ γ'' ~γ = refl

  ConTyRec : ConTyᴿ ConTySyn M
  ConTyRec = record
    { Con = Conᴿ
    ; Ty  = Tyᴿ
    ; •   = refl
    ; ▶   = λ {Γ}{A} → ▶ᴿ {Γ}{A}
    ; U   = λ {Γ} → Uᴿ {Γ}
    ; Π   = λ {Γ}{A}{B} → Πᴿ {Γ}{A}{B}
    }
