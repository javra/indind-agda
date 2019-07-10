{-# OPTIONS --rewriting #-}
module IFM where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵐS : ∀{ℓ' ℓ} B (αc : _ᵃS {ℓ} B)(βc : _ᵃS {ℓ'} B) → Set (ℓ' ⊔ ℓ)
ᵐS U        αc βc = αc → βc
ᵐS (Π̂S T B) αc βc = (τ : T) → ᵐS (B τ) (αc τ) (βc τ)

ᵐc : ∀{ℓ' ℓ} Γc (γc : _ᵃc {ℓ} Γc)(δc : _ᵃc {ℓ'} Γc) → Set (ℓ' ⊔ ℓ)
ᵐc ∙c        γc        δc        = Lift _ ⊤
ᵐc (Γc ▶c B) (γc , αc) (δc , βc) = ᵐc Γc γc δc × ᵐS B αc βc

ᵐt : ∀{ℓ' ℓ Γc B} t {γc : _ᵃc {ℓ} Γc}{δc : _ᵃc {ℓ'} Γc}
       → ᵐc Γc γc δc → ᵐS B ((t ᵃt) γc) ((t ᵃt) δc)   
ᵐt (var vvz)     (γcᵐ , αcᵐ) = αcᵐ
ᵐt (var (vvs t)) (γcᵐ , αcᵐ) = ᵐt (var t) γcᵐ
ᵐt (f $S τ)      γcᵐ         = ᵐt f γcᵐ τ

ᵐP : ∀{ℓ' ℓ Γc} A {γc : _ᵃc {ℓ} Γc}{δc : _ᵃc {ℓ'} Γc}(γcᵐ : ᵐc Γc γc δc)
       → _ᵃP A γc → _ᵃP A δc → Set (ℓ' ⊔ ℓ)
ᵐP {ℓ'}{ℓ} (El a)        γcᵐ α β = Lift (ℓ' ⊔ ℓ) (ᵐt a γcᵐ α ≡ β)
ᵐP        (Π̂P T A)      γcᵐ π ρ = (τ : T) → ᵐP (A τ) γcᵐ (π τ) (ρ τ)
ᵐP        (a ⇒P A) {γc} γcᵐ π ρ = (α : (a ᵃt) γc) → ᵐP A γcᵐ (π α) (ρ (ᵐt a γcᵐ α))

ᵐC : ∀{ℓ' ℓ Γc} Γ {γc : _ᵃc {ℓ} Γc}{δc : _ᵃc {ℓ'} Γc}(γcᵐ : ᵐc Γc γc δc)
       → _ᵃC Γ γc → _ᵃC Γ δc → Set (suc ℓ' ⊔ ℓ)
ᵐC ∙        γcᵐ γ       δ       = Lift _ ⊤
ᵐC (Γ ▶P A) γcᵐ (γ , α) (δ , β) = ᵐC Γ γcᵐ γ δ × ᵐP A γcᵐ α β

ᵐs : ∀{ℓ' ℓ Γc Δc} σ {γc : _ᵃc {ℓ} Γc}{δc : _ᵃc {ℓ'} Γc}
       → ᵐc Γc γc δc → ᵐc Δc (_ᵃs σ γc) ((σ ᵃs) δc)
ᵐs ε       γcᵐ = lift tt
ᵐs (σ , t) γcᵐ = ᵐs σ γcᵐ , ᵐt t γcᵐ

