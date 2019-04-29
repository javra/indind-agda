{-# OPTIONS --rewriting #-}
module IFS where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD

ˢS : ∀{ℓ' ℓ} B {α} → ᵈS {ℓ'}{ℓ} B α → Set (ℓ' ⊔ ℓ)
ˢS U        αᵈ = ∀ x → αᵈ x
ˢS (Π̂S T B) πᵈ = (τ : T) → ˢS (B τ) (πᵈ τ)

ˢc : ∀{ℓ' ℓ} Γc {γc} → ᵈc {ℓ'}{ℓ} Γc γc → Set (ℓ' ⊔ ℓ)
ˢc ∙c        γcᵈ         = Lift _ ⊤
ˢc (Γc ▶c B) (γcᵈ , αcᵈ) = ˢc Γc γcᵈ × ˢS B αcᵈ

ˢt : ∀{ℓ' ℓ Γc B} t {γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ˢc Γc γcᵈ → ˢS B (ᵈt t γcᵈ)
ˢt (var vvz)     (γcˢ , αcˢ) = αcˢ
ˢt (var (vvs t)) (γcˢ , αcˢ) = ˢt (var t) γcˢ
ˢt (f $S τ)      γcˢ         = ˢt f γcˢ τ

ˢP : ∀{ℓ' ℓ Γc} A {γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γcˢ : ˢc Γc γcᵈ){α} → ᵈP A γcᵈ α → Set (ℓ' ⊔ ℓ)
ˢP (El a)        γcˢ {α} αᵈ = ˢt a γcˢ α ≡ αᵈ
ˢP (Π̂P T A)      γcˢ     πᵈ = (τ : T) → ˢP (A τ) γcˢ (πᵈ τ)
ˢP (a ⇒P A) {γc} γcˢ     πᵈ = (α : (a ᵃt) γc) → ˢP A γcˢ (πᵈ _ (ˢt a γcˢ α))

ˢC : ∀{ℓ' ℓ Γc} Γ {γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γcˢ : ˢc Γc γcᵈ){γ} → ᵈC Γ γcᵈ γ → Set (suc ℓ' ⊔ ℓ)
ˢC ∙        γcˢ γᵈ        = Lift _ ⊤
ˢC (Γ ▶P A) γcˢ (γᵈ , αᵈ) = ˢC Γ γcˢ γᵈ × ˢP A γcˢ αᵈ

ˢs : ∀{ℓ' ℓ Γc Δc} σ {γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ˢc Γc γcᵈ → ˢc Δc (ᵈs σ γcᵈ)
ˢs ε       γcˢ = lift tt
ˢs (σ , t) γcˢ = ˢs σ γcˢ , ˢt t γcˢ
