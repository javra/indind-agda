{-# OPTIONS --rewriting #-}
module IFD where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵈS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → Set (suc ℓ' ⊔ ℓ)
ᵈS {ℓ'} U        α = α → Set ℓ'
ᵈS {ℓ'} (Π̂S T B) π = (α : T) → ᵈS {ℓ'} (B α) (π α)

ᵈc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵃc {ℓ} Γc) → Set (suc ℓ' ⊔ ℓ)
ᵈc ∙c             γc       = Lift ⊤
ᵈc {ℓ'} (Γc ▶c B) (γc , α) = ᵈc {ℓ'} Γc γc × ᵈS {ℓ'} B α

ᵈt : ∀{ℓ'}{ℓ}{Γc : SCon}{B : TyS}(t : Tm Γc B)(γc : _ᵃc {ℓ} Γc) → ᵈc {ℓ'} Γc γc → ᵈS {ℓ'} B ((t ᵃt) γc)
ᵈt vz       (γc , α) (γcᵈ , αᵈ) = αᵈ
ᵈt (vs t  ) (γc , α) (γcᵈ , αᴾ) = ᵈt t γc γcᵈ
ᵈt (t $S α) γc       γcᵈ        = ᵈt t γc γcᵈ α

ᵈP : ∀{ℓ' ℓ}{Γc}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(α : (A ᵃP) γc) → Set (ℓ' ⊔ ℓ)
ᵈP {ℓ'}    (Π̂P T B)      γcᵈ π = (α : T) → ᵈP {ℓ'} (B α) γcᵈ (π α)
ᵈP {ℓ'}{ℓ} (El a)   {γc} γcᵈ α = Lift {_}{ℓ' ⊔ ℓ} (ᵈt a γc γcᵈ α)
ᵈP {ℓ'}    (t ⇒P A) {γc} γcᵈ π = (α : (t ᵃt) γc) (αᵈ : ᵈt t γc γcᵈ α) → ᵈP A γcᵈ (π α)

ᵈC : ∀{ℓ' ℓ}{Γc}(Γ : Con Γc)(γc : _ᵃc {ℓ} Γc)(γcᵈ : ᵈc {ℓ'} Γc γc)(γ : (Γ ᵃC) γc) → Set (suc ℓ' ⊔ ℓ)
ᵈC      ∙        γc        γcᵈ        γ       = Lift ⊤
ᵈC {ℓ'} (Γ ▶S B) (γc , αc) (γcᵈ , αᵈ) γ       = ᵈC {ℓ'} Γ γc γcᵈ γ
ᵈC {ℓ'} (Γ ▶P A) γc        γcᵈ        (γ , α) = (ᵈC Γ γc γcᵈ γ)× (ᵈP A γcᵈ α)

ᵈs : ∀{ℓ' ℓ}{Γc Δc}(σ : Sub Γc Δc)(γc : _ᵃc {ℓ} Γc) → ᵈc {ℓ'} Γc γc → ᵈc {ℓ'} Δc ((σ ᵃs) γc)
ᵈs ε       γc γcᵈ = lift tt
ᵈs (σ , t) γc γcᵈ = ᵈs σ γc γcᵈ , ᵈt t γc γcᵈ
