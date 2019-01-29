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

[]Tᴬ : ∀{Γc Δc A}{δ : Sub Γc Δc} → (γc : Γc ᴬc) → ((A [ δ ]T) ᴬP) γc ≡ (A ᴬP) ((δ ᴬs) γc)
[]tᴬ : ∀{Γc Δc A}{a : Tm Δc A}{δ : Sub Γc Δc} → (γc : Γc ᴬc) → ((a [ δ ]t) ᴬt) γc ≡ (a ᴬt) ((δ ᴬs) γc)

[]Tᴬ {A = Π̂P T x} γc = Π≡ refl λ α → []Tᴬ {A = x α} γc
[]Tᴬ {A = El x} γc   = Lift & []tᴬ {a = x} γc
[]Tᴬ {A = x ⇒P A} γc = Π≡ ([]tᴬ {a = x} γc) λ α → []Tᴬ {A = A} γc

[]tᴬ {a = vz} {δ , x} γc   = refl
[]tᴬ {a = vs a} {δ , x} γc = []tᴬ {a = a} γc
[]tᴬ {a = a $S α} {δ} γc   = (λ x → coe x (((a [ δ ]t) ᴬt) γc α)) & (const& ([]tᴬ {a = a} {δ = δ} γc) ⁻¹)
                             ◾ apd (λ f → f α) ([]tᴬ {a = a} {δ = δ} γc)
{-# REWRITE []Tᴬ #-}
{-# REWRITE []tᴬ #-}

wk,ᴬ : ∀{Γc Δc B γc α} → {σ : Sub Γc Δc} → ((wk {B = B} σ) ᴬs) (γc , α) ≡ (σ ᴬs) γc
wk,ᴬ {σ = ε}     = refl
wk,ᴬ {σ = σ , x} = ,≡ wk,ᴬ refl
{-# REWRITE wk,ᴬ #-}

idᴬ : ∀{Γc} → (γc : Γc ᴬc) → (id ᴬs) γc ≡ γc
idᴬ {∙c} γc            = refl
idᴬ {Γc ▶c x} (γc , α) = ,≡ (idᴬ γc) refl
{-# REWRITE idᴬ #-}

∘ᴬ : ∀{Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc} → ((σ ∘ δ) ᴬs) (γc) ≡ (σ ᴬs) ((δ ᴬs) γc)
∘ᴬ {σ = ε}                      = refl
∘ᴬ {σ = σ , x} {δ = δ}{γc = γc} = happly2 _,_ (∘ᴬ {σ = σ} {δ = δ}) ((x ᴬt) ((δ ᴬs) γc))
{-# REWRITE ∘ᴬ #-}