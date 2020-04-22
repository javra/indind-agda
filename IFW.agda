{-# OPTIONS --rewriting #-}
module IFW (Y : Set) (y : Y) where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFE

ʷS : TyS → Set
ʷS U = Y
ʷS (Π̂S T B) = (τ : T) → ʷS (B τ)

ʷc : (Γc : SCon) → _ᵃc {zero} (ᴱc Γc)
ʷc ∙c        = lift tt
ʷc (Γc ▶c B) = ʷc Γc , ʷS B

ʷS= : ∀{Γc}(B : TyS)(t : Tm Γc B) → Set₁
ʷS= U        t = (ᴱt t ᵃt) (ʷc _) ≡ Y
ʷS= (Π̂S T B) t = (τ : T) → ʷS= (B τ) (t $S τ)

ʷP' : (B : TyS) → ʷS B
ʷP' U        = y
ʷP' (Π̂S T B) = λ τ → ʷP' (B τ)

ʷt : ∀{Γc B}(t : Tm Γc B) → (ᴱt t ᵃt) (ʷc _)
ʷt (var vvz)     = ʷP' _
ʷt (var (vvs x)) = ʷt (var x)
ʷt (t $S τ)      = ʷt t

ʷP : ∀{Γc}(A : TyP Γc) → ((ᴱP A) ᵃP) (ʷc Γc)
ʷP (El a)   = ʷt a
ʷP (Π̂P T A) = λ τ → ʷP (A τ)
ʷP (a ⇒P A) = λ α → ʷP A

ʷC : ∀{Γc}(Γ : Con Γc) → ((ᴱC Γ) ᵃC) (ʷc Γc)
ʷC ∙        = lift tt
ʷC (Γ ▶P A) = ʷC Γ , ʷP A
