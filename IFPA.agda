{-# OPTIONS --prop --rewriting #-}
module IFPA where

open import Lib hiding (id; _∘_)
open import StrictLib
open import IF

_ᵖᵃS : ∀{ℓ} → TyS → Set (suc ℓ)
_ᵖᵃS {ℓ} U        = Prop ℓ
_ᵖᵃS {ℓ} (T ⇒̂S B) = T → _ᵖᵃS {ℓ} B

_ᵖᵃc : ∀{ℓ} → SCon → Set (suc ℓ)
∙c ᵖᵃc             = Lift _ ⊤
_ᵖᵃc {ℓ} (Γc ▶c B) = (_ᵖᵃc {ℓ} Γc) × _ᵖᵃS {ℓ} B

_ᵖᵃt : ∀{ℓ Γc B} → Tm Γc B → _ᵖᵃc {ℓ} Γc → _ᵖᵃS {ℓ} B
(var vvz ᵖᵃt)     (γ , α) = α
(var (vvs t) ᵖᵃt) (γ , α) = (var t ᵖᵃt) γ
((t $S α) ᵖᵃt)    γ       = (t ᵖᵃt) γ α

_ᵖᵃP : ∀{ℓ Γc} → TyP Γc → _ᵖᵃc {ℓ} Γc → Prop ℓ
(El a ᵖᵃP)     γ = (a ᵖᵃt) γ
(Π̂P T A ᵖᵃP)   γ = (τ : T) → ((A τ) ᵖᵃP) γ
((a ⇒P A) ᵖᵃP) γ = (a ᵖᵃt) γ → (A ᵖᵃP) γ

_ᵖᵃC : ∀{ℓ Γc} → Con Γc → _ᵖᵃc {ℓ} Γc → Prop ℓ
(∙ ᵖᵃC)        γ = P⊤
((Γ ▶P A) ᵖᵃC) γ = (Γ ᵖᵃC) γ ∧ (A ᵖᵃP) γ

_ᵖᵃs : ∀{ℓ}{Γc Δc} → Sub Γc Δc → _ᵖᵃc {ℓ} Γc → _ᵖᵃc {ℓ} Δc
(ε ᵖᵃs) γ       = lift tt
((σ , t) ᵖᵃs) γ = (σ ᵖᵃs) γ , (t ᵖᵃt) γ

[]tᵖᵃ : ∀{ℓ Γc Δc B}{t : Tm Δc B}{σ : Sub Γc Δc}
       → (γc : _ᵖᵃc {ℓ} Γc) → ((t [ σ ]t) ᵖᵃt) γc ≡ (t ᵖᵃt) ((σ ᵖᵃs) γc)
[]tᵖᵃ {t = var vvz}    {σ , x} γc = refl
[]tᵖᵃ {t = var (vvs a)}{σ , x} γc = []tᵖᵃ {t = var a} γc
[]tᵖᵃ {t = t $S α}     {σ}     γc = happly ([]tᵖᵃ {t = t} γc) α
{-# REWRITE []tᵖᵃ #-}

[]Tᵖᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc Δc} → (γc : _ᵖᵃc {ℓ} Γc) → ((A [ σ ]T) ᵖᵃP) γc ≡ (A ᵖᵃP) ((σ ᵖᵃs) γc)
[]Tᵖᵃ {A = El a}   γc = []tᵖᵃ {t = a} γc
[]Tᵖᵃ {A = Π̂P T A} γc = PΠ≡ refl λ τ → []Tᵖᵃ {A = A τ} γc
[]Tᵖᵃ {A = a ⇒P A} γc = (λ p → _ → p) & []Tᵖᵃ {A = A} γc
{-# REWRITE []Tᵖᵃ #-}

[]Cᵖᵃ : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Δ : Con Δc}{γc : _ᵖᵃc {ℓ} Γc} → ((Δ [ σ ]C) ᵖᵃC) γc ≡ (Δ ᵖᵃC) ((σ ᵖᵃs) γc)
[]Cᵖᵃ {Δ = ∙}      = refl
[]Cᵖᵃ {Δ = Δ ▶P A} = (λ p → p ∧ _) & []Cᵖᵃ
{-# REWRITE []Cᵖᵃ #-}

vs,ᵖᵃ : ∀{ℓ Γc B B'}{x : Tm Γc B}{γc}{α : _ᵖᵃS {ℓ} B'} → (vs x ᵖᵃt) (γc , α) ≡ (x ᵖᵃt) γc
vs,ᵖᵃ {x = var x}  = refl
vs,ᵖᵃ {x = x $S α} = happly (vs,ᵖᵃ {x = x}) α
{-# REWRITE vs,ᵖᵃ #-}

wk,ᵖᵃ : ∀{ℓ Γc Δc B γc}{α : B ᵖᵃS}{σ : Sub Γc Δc} → _ᵖᵃs {ℓ} (wk {B = B} σ) (γc , α) ≡ (σ ᵖᵃs) γc
wk,ᵖᵃ {σ = ε}     = refl
wk,ᵖᵃ {σ = σ , t} = ,≡ wk,ᵖᵃ refl
{-# REWRITE wk,ᵖᵃ #-}

idᵖᵃ : ∀{ℓ Γc} → (γc : _ᵖᵃc {ℓ} Γc) → (id ᵖᵃs) γc ≡ γc
idᵖᵃ {ℓ}{∙c}      γc       = refl
idᵖᵃ {ℓ}{Γc ▶c B} (γc , α) = ,≡ (idᵖᵃ γc) refl
{-# REWRITE idᵖᵃ #-}

wkid : ∀{ℓ Γc B} γc → _ᵖᵃs {ℓ} (wk {B = B} (id {Γc = Γc})) γc ≡ ₁ γc
wkid (γc , α) = refl
{-# REWRITE wkid #-}

∘ᵖᵃ : ∀{ℓ Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc} → _ᵖᵃs {ℓ} (σ ∘ δ) γc ≡ (σ ᵖᵃs) ((δ ᵖᵃs) γc)
∘ᵖᵃ {σ = ε}                      = refl
∘ᵖᵃ {σ = σ , t} {δ = δ}{γc = γc} = happly2 _,_ (∘ᵖᵃ {σ = σ} {δ = δ}) ((t ᵖᵃt) ((δ ᵖᵃs) γc))
{-# REWRITE ∘ᵖᵃ #-}

π₁ᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵖᵃs {ℓ} (π₁ σ) γc ≡ ₁ ((σ ᵖᵃs) γc)
π₁ᵃ {σ = σ , x} = refl
{-# REWRITE π₁ᵃ #-}

π₂ᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵖᵃt {ℓ} (π₂ σ) γc ≡ ₂ ((σ ᵖᵃs) γc)
π₂ᵃ {σ = σ , x} = refl
{-# REWRITE π₂ᵃ #-}
{-
Twkᵃ : ∀{ℓ Γc}{B A γc T} → _ᵖᵃP {ℓ} (Twk {Γc = Γc}{B = B} A) (γc , T) ≡ _ᵖᵃP A γc
Twkᵃ {A = El x}   = refl
Twkᵃ {A = Π̂P T B} = Π≡ refl λ τ → Twkᵃ {A = B τ}
Twkᵃ {A = a ⇒P A} = Π≡ refl λ α → Twkᵃ {A = A}
{-# REWRITE Twkᵃ #-}
-}

_ᵖᵃtP : ∀{ℓ Γc}{Γ : Con Γc}{A}(tP : TmP Γ A){γc}(γ : _ᵖᵃC {ℓ} Γ γc) → _ᵖᵃP {ℓ} A γc
(varP vvzP ᵖᵃtP)     (γ , α) = α
(varP (vvsP x) ᵖᵃtP) (γ , α) = (varP x ᵖᵃtP) γ
((tP $P sP) ᵖᵃtP)    γ       = (tP ᵖᵃtP) γ ((sP ᵖᵃtP) γ)
((tP $̂P τ) ᵖᵃtP)     γ       = (tP ᵖᵃtP) γ τ    

_ᵖᵃsP : ∀{ℓ Γc}{Γ Δ : Con Γc}(σP : SubP Γ Δ){γc}
         → _ᵖᵃC {ℓ} Γ γc → _ᵖᵃC {ℓ} Δ γc
(εP ᵖᵃsP) γ         = ptt
((σP ,P tP) ᵖᵃsP) γ = (σP ᵖᵃsP) γ , (tP ᵖᵃtP) γ

--TODO define ∘Pᵃ, π₁Pᵃ, π₂Pᵃ
