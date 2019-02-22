{-# OPTIONS --rewriting #-}
module IFS where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD

ˢS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → ᵈS {ℓ'} B α → Set (ℓ' ⊔ ℓ)
ˢS U        T Tᵈ = (α : T) → Tᵈ α
ˢS (Π̂S T B) π πᵈ = (α : T) → ˢS (B α) (π α) (πᵈ α)

ˢc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵃc {ℓ} Γc) → ᵈc {ℓ'} Γc γc → Set (ℓ' ⊔ ℓ)
ˢc ∙c        γc        γcᵈ         = Lift ⊤
ˢc (Γc ▶c B) (γc , αc) (γcᵈ , αcᵈ) = ˢc Γc γc γcᵈ × ˢS B αc αcᵈ

ˢt : ∀{ℓ' ℓ}{Γc : SCon}{B : TyS}(t : Tm Γc B)(γc : _ᵃc {ℓ} Γc)(γcᵈ : ᵈc {ℓ'} Γc γc)(γcˢ : ˢc Γc γc γcᵈ) → ˢS B ((t ᵃt) γc) (ᵈt t γc γcᵈ)
ˢt vz       (γc , αc) (γcᵈ , αcᵈ) (γcˢ , αcˢ) = αcˢ
ˢt (vs t)   (γc , αc) (γcᵈ , αcᵈ) (γcˢ , αcˢ) = ˢt t γc γcᵈ γcˢ
ˢt (t $S α) γc        γcᵈ         γcˢ         = ˢt t γc γcᵈ γcˢ α
