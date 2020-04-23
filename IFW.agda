{-# OPTIONS --rewriting #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFE

module IFW where

ʷS : TyS → Set₁
ʷS U        = Set
ʷS (Π̂S T B) = (τ : T) → ʷS (B τ)

ʷc : (Γc : SCon)(γc : ᴱc Γc ᵃc) → ᵈc {zero}{suc zero} (ᴱc Γc) γc
ʷc ∙c        γc       = lift tt
ʷc (Γc ▶c B) (γc , α) = ʷc Γc γc , λ _ → ʷS B

ʷP' : (B : TyS) → ʷS B
ʷP' U        = ⊤
ʷP' (Π̂S T B) = λ τ → ʷP' (B τ)

ʷt : ∀{Γc B}(t : Tm Γc B){γc : ᴱc Γc ᵃc}(α : (ᴱt t ᵃt) γc)
     → ᵈt (ᴱt t) (ʷc Γc γc) α
ʷt (var vvz)     {γc , β} αʷ = ʷP' _
ʷt (var (vvs x))          αʷ = ʷt (var x) αʷ
ʷt (t $S τ)               αʷ = ʷt t αʷ

ʷP : ∀{Γc}(A : TyP Γc){γc : ᴱc Γc ᵃc}(α : (ᴱP A ᵃP) γc)
     → ᵈP (ᴱP A) (ʷc Γc γc) α
ʷP (El a)   α = ʷt a α
ʷP (Π̂P T A) α = λ τ → ʷP (A τ) (α τ)
ʷP (a ⇒P A) α = λ β βʷ → ʷP A (α β)

ʷC : ∀{Γc}(Γ : Con Γc){γc}(γ : (ᴱC Γ ᵃC) γc)
      → ᵈC (ᴱC Γ) (ʷc Γc γc) γ
ʷC ∙        γ       = lift tt
ʷC (Γ ▶P A) (γ , α) = ʷC Γ γ , ʷP A α


