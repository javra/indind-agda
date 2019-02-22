{-# OPTIONS --rewriting #-}
module IFS where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD

ˢS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → ᵈS {ℓ'} B α → Set (ℓ' ⊔ ℓ)
ˢS U        T Tᵈ = (α : T) → Tᵈ α
ˢS (Π̂S T B) π πᵈ = (α : T) → ˢS (B α) (π α) (πᵈ α)

ˢc : ∀{ℓ' ℓ}(Γc : SCon){γc : _ᵃc {ℓ} Γc} → ᵈc {ℓ'} Γc γc → Set (ℓ' ⊔ ℓ)
ˢc ∙c        γcᵈ         = Lift ⊤
ˢc (Γc ▶c B) (γcᵈ , αcᵈ) = ˢc Γc γcᵈ × ˢS B _ αcᵈ

ˢt : ∀{ℓ' ℓ}{Γc : SCon}{B : TyS}(t : Tm Γc B){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ) → ˢS B ((t ᵃt) γc) (ᵈt t γc γcᵈ)
ˢt vz       (γcˢ , αcˢ) = αcˢ
ˢt (vs t)   (γcˢ , αcˢ) = ˢt t γcˢ
ˢt (t $S α) γcˢ         = ˢt t γcˢ α

ˢP : ∀{ℓ' ℓ}{Γc : SCon}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ)(α : (A ᵃP) γc)(αᵈ : ᵈP A γcᵈ α) → Set (ℓ' ⊔ ℓ)
ˢP (Π̂P T A)      γcˢ π πᵈ = (α : T) → ˢP (A α) γcˢ (π α) (πᵈ α)
ˢP (El a)        γcˢ α αᵈ = lift (ˢt a γcˢ α) ≡ αᵈ
ˢP (t ⇒P A) {γc} γcˢ α αᵈ = (x : (t ᵃt) γc) → ˢP A γcˢ (α x) (αᵈ x (ˢt t γcˢ x))

ˢC : ∀{ℓ' ℓ}{Γc}(Γ : Con Γc){γc : _ᵃc {ℓ} Γc}{γcᵈ : ᵈc {ℓ'} Γc γc}(γcˢ : ˢc Γc γcᵈ){γ : (Γ ᵃC) γc}(γᵈ : ᵈC Γ γcᵈ γ) → Set (suc ℓ' ⊔ ℓ)
ˢC ∙        γcˢ γᵈ                 = Lift ⊤
ˢC (Γ ▶S B) (γcˢ , αcˢ) γᵈ         = ˢC Γ γcˢ γᵈ
ˢC (Γ ▶P A) γcˢ         (γᵈ , αᵈ)  = Σ (ˢC Γ γcˢ γᵈ) λ γˢ → ˢP A γcˢ _ αᵈ

ˢs : ∀{ℓ' ℓ}{Γc Δc}(σ : Sub Γc Δc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc) → ˢc Γc γcᵈ → ˢc Δc (ᵈs σ γc γcᵈ)
ˢs ε γcᵈ γcˢ       = lift tt
ˢs (σ , t) γcᵈ γcˢ = ˢs σ γcᵈ γcˢ , ˢt t γcˢ
