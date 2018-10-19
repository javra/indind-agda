
module IIReductionExamples.ConTyEq2 where

open import Lib


record Model : Set₁ where
  field
    Con : Set
    Ty  : Con → Set
    ∙   : Con
    _▶_ : (Γ : Con)(A : Ty Γ) → Con
    U   : (Γ : Con) → Ty Γ
    Sg  : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ
    eq  : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Γ ▶ Sg Γ A B ≡ Γ ▶ A ▶ B
  infixl 5 _▶_

------------------------------------------------------------

infixl 5 _▶_

data Con : Set
data Ty  : Set

data Con where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Ty where
  U  : Con → Ty
  Sg : Con → Ty → Ty → Ty

------------------------------------------------------------

Conw : Con → Set
Tyw  : Ty → Con → Set
Conw ∙          = ⊤
Conw (Γ ▶ A)    = Conw Γ × Tyw A Γ
Tyw  (U Γ)      = λ Δ → Conw Γ × (Γ ≡ Δ)
Tyw  (Sg Γ A B) = λ Δ → Conw Γ × Tyw A Γ × Tyw B (Γ ▶ A)

------------------------------------------------------------
