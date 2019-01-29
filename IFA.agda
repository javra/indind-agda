{-# OPTIONS --rewriting #-}
module IFA where

open import Lib hiding (id; _∘_)
open import IFSyntax

_ᴬS : TyS → Set₁
U ᴬS = Set
Π̂S T A ᴬS = (α : T) → (A α) ᴬS

_ᴬc : SCon → Set₁
∙c ᴬc = Lift ⊤
(Γ ▶c A) ᴬc = Γ ᴬc × A ᴬS

_ᴬt : {Γ : SCon}{A : TyS} → Tm Γ A → Γ ᴬc → A ᴬS
(vz ᴬt) (γ , α) = α
(vs t ᴬt) (γ , α) = (t ᴬt) γ
((t $S α) ᴬt) γ = (t ᴬt) γ α

_ᴬP : {Γc : SCon} → TyP Γc → (γ : Γc ᴬc) → Set₁
(Π̂P T A ᴬP) γ   = (α : T) → ((A α) ᴬP) γ
(El a ᴬP) γ     = Lift ((a ᴬt) γ)
((a ⇒P B) ᴬP) γ = (a ᴬt) γ → (B ᴬP) γ

_ᴬC : {Γc : SCon} → Con Γc → Γc ᴬc → Set₁
(∙ ᴬC) γ = Lift ⊤
((Γ ▶S A) ᴬC) (γ , _) = (Γ ᴬC) γ × A ᴬS
((Γ ▶P A) ᴬC) γ       = (Γ ᴬC) γ × (A ᴬP) γ

_ᴬs : {Γc Δc : SCon} → Sub Γc Δc → Γc ᴬc → Δc ᴬc
(ε ᴬs) γ       = lift tt
((σ , t) ᴬs) γ = (σ ᴬs) γ , (t ᴬt) γ

[]TᴬS : ∀{Γc Δc A}{δ : Sub Γc Δc} → (γ : Γc ᴬc) → ((A [ δ ]T) ᴬP) γ ≡ (A ᴬP) ((δ ᴬs) γ)
[]tᴬS : ∀{Γc Δc A}{a : Tm Δc A}{δ : Sub Γc Δc} → (γ : Γc ᴬc) → ((a [ δ ]t) ᴬt) γ ≡ (a ᴬt) ((δ ᴬs) γ)

[]TᴬS {A = Π̂P T x} γ = Π≡ refl λ α → []TᴬS {A = x α} γ
[]TᴬS {A = El x} γ   = Lift & []tᴬS {a = x} γ
[]TᴬS {A = x ⇒P A} γ = Π≡ ([]tᴬS {a = x} γ) λ α → []TᴬS {A = A} γ

[]tᴬS {a = vz} {δ , x} γ = refl
[]tᴬS {a = vs a} {δ , x} γ = []tᴬS {a = a} γ
[]tᴬS {a = a $S α} {δ} γ = (λ x → coe x (((a [ δ ]t) ᴬt) γ α)) & (const& ([]tᴬS {a = a} {δ = δ} γ) ⁻¹) ◾ apd (λ f → f α) ([]tᴬS {a = a} {δ = δ} γ)
{-# REWRITE []TᴬS #-}
