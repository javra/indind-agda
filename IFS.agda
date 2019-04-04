{-# OPTIONS --rewriting #-}
module IFS where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD

ˢS : ∀{ℓ' ℓ}(B : TyS){α : _ᵃS {ℓ} B} → ᵈS {ℓ'} B α → Set (ℓ' ⊔ ℓ)
ˢS U        {α} αᵈ = (x : α) → αᵈ x
ˢS (Π̂S T B)     πᵈ = (τ : T) → ˢS (B τ) (πᵈ τ)

ˢc : ∀{ℓ' ℓ}(Γc : SCon){γc : _ᵃc {ℓ} Γc} → ᵈc {ℓ'} Γc γc → Set (ℓ' ⊔ ℓ)
ˢc ∙c        γcᵈ         = Lift _ ⊤
ˢc (Γc ▶c B) (γcᵈ , αcᵈ) = ˢc Γc γcᵈ × ˢS B αcᵈ

ˢt : ∀{ℓ' ℓ}{Γc : SCon}{B : TyS}(t : Tm Γc B){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ)
     → ˢS B (ᵈt t γcᵈ)
ˢt (var vvz)     (γcˢ , αcˢ) = αcˢ
ˢt (var (vvs t)) (γcˢ , αcˢ) = ˢt (var t) γcˢ
ˢt (t $S α)      γcˢ         = ˢt t γcˢ α

ˢP : ∀{ℓ' ℓ}{Γc : SCon}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ)(α : (A ᵃP) γc)(αᵈ : ᵈP A γcᵈ α) → Set (ℓ' ⊔ ℓ)
ˢP (Π̂P T A)      γcˢ π πᵈ = (τ : T) → ˢP (A τ) γcˢ (π τ) (πᵈ τ)
ˢP (El a)        γcˢ α αᵈ = lift (ˢt a γcˢ α) ≡ αᵈ
ˢP (t ⇒P A) {γc} γcˢ α αᵈ = (x : (t ᵃt) γc) → ˢP A γcˢ (α x) (αᵈ x (ˢt t γcˢ x))

ˢC : ∀{ℓ' ℓ}{Γc}(Γ : Con Γc){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ){γ : (Γ ᵃC) γc}(γᵈ : ᵈC Γ γcᵈ γ) → Set (suc ℓ' ⊔ ℓ)
ˢC ∙        γcˢ γᵈ        = Lift _ ⊤
ˢC (Γ ▶P A) γcˢ (γᵈ , αᵈ) = Σ (ˢC Γ γcˢ γᵈ) λ γˢ → ˢP A γcˢ _ αᵈ

ˢs : ∀{ℓ' ℓ}{Γc Δc}(σ : Sub Γc Δc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc) → ˢc Γc γcᵈ → ˢc Δc (ᵈs σ γc γcᵈ)
ˢs ε γcᵈ γcˢ       = lift tt
ˢs (σ , t) γcᵈ γcˢ = ˢs σ γcᵈ γcˢ , ˢt t γcˢ
