{-# OPTIONS --without-K #-}

{-
  Constructing the recursor (without uniqueness so far) for ConTy
  inductive-inductive example. No UIP, funext, propext, quotients or
  recursion-recursion are used.
-}

module IIReductionExamples.ConTyRec where

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


-- Presyntax
--------------------------------------------------------------------------------

-- I use Agda inductive types and patterns because postulated records
-- are impossible to normalize in goal types and hence completely
-- unreadable. Defined eliminators on native inductive types also look
-- horrible in goals, so that's a no for them as well.

-- Nonetheless, I try to format models so that it becomes apparent
-- that I don't cheat, e. g. by using recursion-recursion.

infixl 5 _▶_

data Con : Set
data Ty  : Set

data Con where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Ty where
  U : Con → Ty
  Π : Con → Ty → Ty → Ty

-- Well-formedness predicates
--------------------------------------------------------------------------------

-- It is easy to show that w is propositional, but we don't actually
-- need that proof here. Also, note that Tyw Γ A implies Conw Γ.
Conw : (Γ : Con) → Set
Tyw  : (A : Ty)  → Con → Set
Conw   ∙         = ⊤
Conw   (Γ ▶ A)   = Conw Γ × Tyw A Γ
Tyw    (U Γ)     = λ Δ → Conw Γ × (Γ ≡ Δ)
Tyw    (Π Γ A B) = λ Δ → Conw Γ × Tyw A Γ × Tyw B (Γ ▶ A) × (Γ ≡ Δ)

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

ConTySyn : ConTy {zero}
ConTySyn = record {
    Con = ∃ Conw
  ; Ty  = λ {(Γ , _) → Σ Ty λ A → Tyw A Γ}
  ; ∙   = ∙ , tt
  ; _▶_ = λ {(Γ , Γw) (A , Aw) → (Γ ▶ A) , Γw , Aw}
  ; U   = λ {(Γ , Γw) → U Γ , Γw , refl}
  ; Π   = λ {(Γ , Γw)(A , Aw)(B , Bw) → Π Γ A B , Γw , Aw , Bw , refl}}

module Syn = ConTy ConTySyn

-- Recursion for inductive-inductive syntax
--------------------------------------------------------------------------------

module _ {α}(M : ConTy {α}) where
  module M = ConTy M

  -- Logical relation between the presyntax and the M model expressing
  -- that presyntactic and semantic values have the same structure
  Con~ : (Γ : Con) → M.Con → Set α
  Ty~  : (A : Ty)  → ∀ γ → M.Ty γ → Set α
  Con~   ∙           γ = γ ≡ M.∙
  Con~   (Γ ▶ A)     γ = ∃₂ λ γ₀ α → Con~ Γ γ₀ × Ty~ A γ₀ α × (γ ≡ γ₀ M.▶ α)
  Ty~    (U Γ)       γ α = Con~ Γ γ × (α ≡ M.U γ)
  Ty~    (Π Γ A B)   γ α = Con~ Γ γ × ∃₂ λ α₀ α₁ → Ty~ A γ α₀ × Ty~ B (γ M.▶ α₀) α₁ × (α ≡ M.Π γ α₀ α₁)

  -- Semantic values with the same presyntactic structure are equal
  Γ~≡ : (Γ : Con) → ∀ γ γ' → Con~ Γ γ  → Con~ Γ γ' → γ ≡ γ'
  A~≡ : (A : Ty)  → ∀ γ α α' → Ty~ A γ α → Ty~ A γ α' → α ≡ α'
  Γ~≡   ∙           γ γ' ~γ ~γ' = ~γ ◾ ~γ' ⁻¹
  Γ~≡   (Γ ▶ A)     _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                 | refl = _&_ (γ' M.▶_) (A~≡ A γ α α' ~α ~α')
  A~≡   (U Γ)       γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹
  A~≡   (Π Γ A B)   γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
                          (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl) with A~≡ A γ α₀ α₀' ~α₀ ~α₀'
  ...                 | refl = _&_ (M.Π γ α₀') (A~≡ B (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

  -- ... which equality is refl in the degenerate case
  Γ~refl : (Γ : Con) → ∀ γ ~γ → Γ~≡ Γ γ γ ~γ ~γ ≡ refl
  A~refl : (A : Ty)  → ∀ γ α ~α → A~≡ A γ α α ~α ~α ≡ refl
  Γ~refl   ∙           γ refl = refl
  Γ~refl   (Γ ▶ A)     _ (γ , α , ~γ , ~α , refl)
                         rewrite Γ~refl Γ γ ~γ | A~refl A γ α ~α = refl
  A~refl   (U Γ)       γ _ (~γ , refl) = refl
  A~refl   (Π Γ A B)   γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
                         rewrite A~refl A γ α₀ ~α₀ | A~refl B (γ M.▶ α₀) α₁ ~α₁ = refl

  -- Interpretation of the well-formed presyntax in M.
  -- We have redundant ~ witnesses, but we must always return the topmost ones,
  -- which is the canonical choice, in order to avoid UIP for recursion.
  ⟦Con⟧ : (Γ : Con) → Conw Γ → ∃ λ γ → Con~ Γ γ
  ⟦Ty⟧  : (A : Ty) → ∀ Γ → Tyw A Γ → ∃₂ λ γ α → Con~ Γ γ × Ty~ A γ α
  ⟦Con⟧   ∙           _ = M.∙ , refl
  ⟦Con⟧   (Γ ▶ A)     (Γw , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl = (γ M.▶ α) , (γ , α , ~γ , ~α , refl)
  ⟦Ty⟧ (U Γ)     _ (Γw , refl) with ⟦Con⟧ Γ Γw
  ...                   | (γ , ~γ) = γ , M.U γ , ~γ , ~γ , refl
  ⟦Ty⟧ (Π Γ A B) Δ (Γw , Aw , Bw , refl) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ...                   | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ...                   | refl with A~≡ A γ'' α α' ~α ~α'
  ...                   | refl = γ , M.Π γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

  -- Recursion
  Conᴿ : Syn.Con → M.Con
  Conᴿ (Γ , Γw) = ₁ (⟦Con⟧ Γ Γw)

  Tyᴿ : ∀ {Γ} → Syn.Ty Γ → M.Ty (Conᴿ Γ)
  Tyᴿ {Γ , Γw} (A , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | γ , ~γ | γ' , α , ~γ' , ~α with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = α

  ▶ᴿ : ∀ {Γ A} → Conᴿ (Γ Syn.▶ A) ≡ Conᴿ Γ M.▶ Tyᴿ A
  ▶ᴿ {Γ , Γw}{A , Aw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = refl

  Uᴿ : ∀ {Γ} → Tyᴿ (Syn.U Γ) ≡ M.U (Conᴿ Γ)
  Uᴿ {Γ , Γw} with ⟦Con⟧ Γ Γw
  ... | γ , ~γ rewrite Γ~refl Γ γ ~γ = refl

  Πᴿ : ∀ {Γ A B} → Tyᴿ (Syn.Π Γ A B) ≡ M.Π (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
  Πᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ... | refl with A~≡ A γ'' α α' ~α ~α'
  ... | refl rewrite Γ~refl Γ γ'' ~γ = refl

  ConTyRec : ConTyᴿ ConTySyn M
  ConTyRec = record
    { Con = Conᴿ
    ; Ty  = Tyᴿ
    ; •   = refl
    ; ▶   = λ {Γ}{A} → ▶ᴿ {Γ}{A}
    ; U   = λ {Γ} → Uᴿ {Γ}
    ; Π   = λ {Γ}{A}{B} → Πᴿ {Γ}{A}{B}
    }
