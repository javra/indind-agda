{-# OPTIONS --rewriting #-}
module IFM where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵐc : (Γ : SCon) → Γ ᵃc → Γ ᵃc → Set
ᵐS : (B : TyS) → B ᵃS → B ᵃS → Set
ᵐP : ∀{Γ}(A : TyP Γ){γ₀ γ₁} → ᵐc Γ γ₀ γ₁ → (A ᵃP) γ₀ → (A ᵃP) γ₁ → Set
ᵐt : ∀{Γ}{B}(t : Tm Γ B){γ₀ γ₁} → ᵐc Γ γ₀ γ₁ → ᵐS B ((t ᵃt) γ₀) ((t ᵃt) γ₁)

ᵐc ∙c       γ₀        γ₁        = Lift ⊤
ᵐc (Γ ▶c B) (γ₀ , α₀) (γ₁ , α₁) = Σ (ᵐc Γ γ₀ γ₁) λ μ → ᵐS B α₀ α₁

ᵐS U        β₀ β₁ = β₀ → β₁
ᵐS (Π̂S T B) β₀ β₁ = (α : T) → ᵐS (B α) (β₀ α) (β₁ α)

ᵐP (Π̂P T B) {γ₀}{γ₁} γᵐ f₀ f₁      = (α : T) → ᵐP (B α) γᵐ (f₀ α) (f₁ α)
ᵐP (El a)   γᵐ (lift α₀) (lift α₁) = ᵐt a γᵐ α₀ ≡ α₁ -- ?????
ᵐP (t ⇒P A) γᵐ f₀ f₁               = (x : (t ᵃt) _) → ᵐP A γᵐ (f₀ x) (f₁ (ᵐt t γᵐ x))

ᵐt vz       (γᵐ , αᵐ) = αᵐ
ᵐt (vs t)   (γᵐ , αᵐ) = ᵐt t γᵐ
ᵐt (t $S α) γᵐ        = ᵐt t γᵐ α
