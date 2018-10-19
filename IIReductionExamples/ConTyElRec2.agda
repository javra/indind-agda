

module IIReductionExamples.ConTyElRec2 where

open import Lib renaming (_Σ,_ to _,_)

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
    El   : (Γ : Con) → Ty (Γ ▶ U Γ)

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
    El  : ∀{Γ} → Ty (M.El Γ) ≡ tr N.Ty (ap (Con Γ N.▶_) (U ⁻¹) ◾ ▶ ⁻¹) (N.El (Con Γ))

-- Presyntax
--------------------------------------------------------------------------------

infixl 6 _▶_

data Con : Set
data Ty  : Set

data Con where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Ty where
  U  : Con → Ty
  Π  : Con → Ty → Ty → Ty
  El : Con → Ty

-- Well-formedness predicates
--------------------------------------------------------------------------------

Conw : (Γ : Con) → Set
Tyw  : (A : Ty)  → Con → Set
Conw   ∙         = ⊤
Conw   (Γ ▶ A)   = Conw Γ × Tyw A Γ
Tyw    (U Γ)     = λ Δ → Conw Γ × (Γ ≡ Δ)
Tyw    (Π Γ A B) = λ Δ → Conw Γ × Tyw A Γ × Tyw B (Γ ▶ A) × (Γ ≡ Δ)
Tyw    (El Γ)    = λ Δ → (Γ ▶ U Γ) ≡ Δ

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

ConTySyn : ConTy {zero}
ConTySyn = record {
    Con = ∃ Conw
  ; Ty  = λ {(Γ , _) → Σ Ty λ A → Tyw A Γ}
  ; ∙   = ∙ , tt
  ; _▶_ = λ {(Γ , Γw) (A , Aw) → (Γ ▶ A) , Γw , Aw}
  ; U   = λ {(Γ , Γw) → U Γ , Γw , refl}
  ; Π   = λ {(Γ , Γw)(A , Aw)(B , Bw) → Π Γ A B , Γw , Aw , Bw , refl}
  ; El  = λ {(Γ , Γw) → (El Γ) , refl}}

module Syn = ConTy ConTySyn


-- Recursion for inductive-inductive syntax
--------------------------------------------------------------------------------

module _ {α}(M : ConTy {α}) where
  module M = ConTy M

  Con~ : (Γ : Con) → M.Con → Set α
  Ty~  : (A : Ty)  → ∀ γ → M.Ty γ → Set α
  Con~ ∙           γ = γ ≡ M.∙
  Con~ (Γ ▶ A)     γ = ∃₂ λ γ₀ α → Con~ Γ γ₀ × Ty~ A γ₀ α × (γ ≡ γ₀ M.▶ α)
  Ty~  (U Γ)       γ α = Con~ Γ γ × (α ≡ M.U γ)
  Ty~  (Π Γ A B)   γ α = Con~ Γ γ × ∃₂ λ α₀ α₁ → Ty~ A γ α₀ × Ty~ B (γ M.▶ α₀) α₁ × (α ≡ M.Π γ α₀ α₁)
  Ty~  (El Γ)      γ α = {!!}



-- we need quotients!!
-- Id : (a : Tm Γ U) → Tm Γ (El a) → Tm Γ (El a) → Ty Γ
-- Id a t u = ?
-- Reflect : Tm Γ (Id a t u) → t ≡ u

--   -- -- Γ~≡ : (Γ : Con) → ∀ Γ* Γ*' → Con~ Γ Γ*  → Con~ Γ Γ*' → Γ* ≡ Γ*'
--   -- -- A~≡ : (A : Ty)  → ∀ Γⁱ A* A*' → Ty~ A Γⁱ A* → Ty~ A Γⁱ A*' → A* ≡ A*'
--   -- -- Γ~≡ ∙       Γ* Γ*' Γ~ Γ~' = Γ~ ⁻¹ ◾ Γ~'
--   -- -- Γ~≡ (Γ ▶ A) _ _ (Γ* , Γ~ , A* , A~ , refl) (Γ*' , Γ~' , A*' , A~' , refl)  = {!!}
--   -- -- A~≡ (U Γ) Γⁱ A* A*' (Γ~ , refl) (Γ~' , refl) = {!!}
--   -- -- A~≡ (Π Γ A B) Γⁱ _ _ (Γ~ , A* , A~ , B* , B~ , refl) (Γ~' , A*' , A~' , B*' , B~' , refl) = {!!}
--   -- -- A~≡ (El Γ) _  T* T*' (Γ* , Γ~ , refl , refl) (Γ*' , Γ~' , foo , bar) = {!!}

--   -- Γ~≡ : (Γ : Con) → ∀ Γ* Γ*' → Con~ Γ Γ*  → Con~ Γ Γ*' → Γ* ≡ Γ*'
--   -- A~≡ : (A : Ty)  → ∀ Γⁱ Γⁱ' A* A*' → Ty~ A Γⁱ A* → Ty~ A Γⁱ' A*' → ∃ λ Γⁱ≡ → tr M.Ty Γⁱ≡ A* ≡ A*'
--   -- Γ~≡ ∙       Γ* Γ*' Γ~ Γ~' = Γ~ ⁻¹ ◾ Γ~'
--   -- Γ~≡ (Γ ▶ A) _ _ (Γ* , Γ~ , A* , A~ , refl) (Γ*' , Γ~' , A*' , A~' , refl) with A~≡ A  Γ* Γ*' A* A*' A~ A~'
--   -- ... | refl , refl = refl
--   -- A~≡ (U Γ) Γⁱ Γⁱ' A* A*' (Γ~ , refl) (Γ~' , refl) with Γ~≡ Γ Γⁱ Γⁱ' Γ~ Γ~'
--   -- ... | refl = refl , refl
--   -- A~≡ (Π Γ A B) Γⁱ Γⁱ' _ _ (Γ~ , A* , A~ , B* , B~ , refl) (Γ~' , A*' , A~' , B*' , B~' , refl)
--   --   with A~≡ B (Γⁱ M.▶ A*) (Γⁱ' M.▶ A*') B* B*' B~ B~'
--   -- ... | foo = {!!}
--   -- A~≡ (El Γ)    _  _   T* T*' (Γ* , Γ~ , refl , refl) (Γ*' , Γ~' , refl , refl) with Γ~≡ Γ Γ* Γ*' Γ~ Γ~'
--   -- ... | refl = refl , refl

--   -- -- Semantic values with the same presyntactic structure are equal
--   -- Γ~≡ : (Γ : Con) → ∀ γ γ' → Con~ Γ γ  → Con~ Γ γ' → γ ≡ γ'
--   -- A~≡ : (A : Ty)  → ∀ γ α α' → Ty~ A γ α → Ty~ A γ α' → α ≡ α'
--   -- Γ~≡   ∙           γ γ' ~γ ~γ' = ~γ ◾ ~γ' ⁻¹
--   -- Γ~≡   (Γ ▶ A)     _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl) with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ...                 | refl = ap (γ' M.▶_) (A~≡ A γ α α' ~α ~α')
--   -- A~≡   (U Γ)       γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹
--   -- A~≡   (Π Γ A B)   γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
--   --                         (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl) with A~≡ A γ α₀ α₀' ~α₀ ~α₀'
--   -- ...                 | refl = ap (M.Π γ α₀') (A~≡ B (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

--   -- -- ... which equality is refl in the degenerate case
--   -- Γ~refl : (Γ : Con) → ∀ γ ~γ → Γ~≡ Γ γ γ ~γ ~γ ≡ refl
--   -- A~refl : (A : Ty)  → ∀ γ α ~α → A~≡ A γ α α ~α ~α ≡ refl
--   -- Γ~refl   ∙           γ refl = refl
--   -- Γ~refl   (Γ ▶ A)     _ (γ , α , ~γ , ~α , refl)
--   --                        rewrite Γ~refl Γ γ ~γ | A~refl A γ α ~α = refl
--   -- A~refl   (U Γ)       γ _ (~γ , refl) = refl
--   -- A~refl   (Π Γ A B)   γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
--   --                        rewrite A~refl A γ α₀ ~α₀ | A~refl B (γ M.▶ α₀) α₁ ~α₁ = refl

--   -- -- Interpretation of the well-formed presyntax in M.
--   -- -- We have redundant ~ witnesses, but we must always return the topmost ones,
--   -- -- which is the canonical choice, in order to avoid UIP for recursion.
--   -- ⟦Con⟧ : (Γ : Con) → Conw Γ → ∃ λ γ → Con~ Γ γ
--   -- ⟦Ty⟧  : (A : Ty) → ∀ Γ → Tyw A Γ → ∃₂ λ γ α → Con~ Γ γ × Ty~ A γ α
--   -- ⟦Con⟧   ∙           _ = M.∙ , refl
--   -- ⟦Con⟧   (Γ ▶ A)     (Γw , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
--   -- ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ...                   | refl = (γ M.▶ α) , (γ , α , ~γ , ~α , refl)
--   -- ⟦Ty⟧ (U Γ)     _ (Γw , refl) with ⟦Con⟧ Γ Γw
--   -- ...                   | (γ , ~γ) = γ , M.U γ , ~γ , ~γ , refl
--   -- ⟦Ty⟧ (Π Γ A B) Δ (Γw , Aw , Bw , refl) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
--   -- ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ...                   | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
--   -- ...                   | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
--   -- ...                   | refl with A~≡ A γ'' α α' ~α ~α'
--   -- ...                   | refl = γ , M.Π γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

--   -- -- Recursion
--   -- Conᴿ : Syn.Con → M.Con
--   -- Conᴿ (Γ , Γw) = ₁ (⟦Con⟧ Γ Γw)

--   -- Tyᴿ : ∀ {Γ} → Syn.Ty Γ → M.Ty (Conᴿ Γ)
--   -- Tyᴿ {Γ , Γw} (A , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
--   -- ... | γ , ~γ | γ' , α , ~γ' , ~α with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ... | refl = α

--   -- ▶ᴿ : ∀ {Γ A} → Conᴿ (Γ Syn.▶ A) ≡ Conᴿ Γ M.▶ Tyᴿ A
--   -- ▶ᴿ {Γ , Γw}{A , Aw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
--   -- ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ... | refl = refl

--   -- Uᴿ : ∀ {Γ} → Tyᴿ (Syn.U Γ) ≡ M.U (Conᴿ Γ)
--   -- Uᴿ {Γ , Γw} with ⟦Con⟧ Γ Γw
--   -- ... | γ , ~γ rewrite Γ~refl Γ γ ~γ = refl

--   -- Πᴿ : ∀ {Γ A B} → Tyᴿ (Syn.Π Γ A B) ≡ M.Π (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
--   -- Πᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
--   -- ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
--   -- ... | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
--   -- ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
--   -- ... | refl with A~≡ A γ'' α α' ~α ~α'
--   -- ... | refl rewrite Γ~refl Γ γ'' ~γ = refl

--   -- ConTyRec : ConTyᴿ ConTySyn M
--   -- ConTyRec = record
--   --   { Con = Conᴿ
--   --   ; Ty  = Tyᴿ
--   --   ; •   = refl
--   --   ; ▶   = λ {Γ}{A} → ▶ᴿ {Γ}{A}
--   --   ; U   = λ {Γ} → Uᴿ {Γ}
--   --   ; Π   = λ {Γ}{A}{B} → Πᴿ {Γ}{A}{B}
--   --   }
