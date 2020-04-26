{-# OPTIONS --rewriting #-}

module IFE where

open import Lib hiding (id; _∘_)
open import IF

ᴱc : SCon → SCon
ᴱc ∙c        = ∙c
ᴱc (Γc ▶c x) = ᴱc Γc ▶c U

ᴱv : ∀{Γc B} → Var Γc B → Var (ᴱc Γc) U
ᴱv vvz     = vvz
ᴱv (vvs x) = vvs (ᴱv x)

ᴱt : ∀{Γc B} → Tm Γc B → Tm (ᴱc Γc) U
ᴱt (var x)  = var (ᴱv x)
ᴱt (t $S τ) = ᴱt t

ᴱP : ∀{Γc} → TyP Γc → TyP (ᴱc Γc)
ᴱP (El a)   = El (ᴱt a)
ᴱP (Π̂P T A) = Π̂P T λ τ → ᴱP (A τ)
ᴱP (a ⇒P A) = ᴱt a ⇒P ᴱP A

ᴱC : ∀{Γc} → Con Γc → Con (ᴱc Γc)
ᴱC ∙        = ∙
ᴱC (Γ ▶P A) = ᴱC Γ ▶P ᴱP A

ᴱs : ∀{Γc Δc} → Sub Γc Δc → Sub (ᴱc Γc) (ᴱc Δc)
ᴱs ε       = ε
ᴱs (σ , t) = ᴱs σ , ᴱt t

[]tᴱ : ∀{Γc Δc B}{t : Tm Δc B}{σ : Sub Γc Δc}
       → ᴱt (t [ σ ]t) ≡ ᴱt t [ ᴱs σ ]t
[]tᴱ {t = var vvz}     {σ , x'} = refl
[]tᴱ {t = var (vvs x)} {σ , x'} = []tᴱ {t = var x}
[]tᴱ {t = t $S τ}      {σ}      = []tᴱ {t = t}
{-# REWRITE []tᴱ #-}

[]Tᴱ : ∀{Γc Δc A}{σ : Sub Γc Δc}
       → ᴱP (A [ σ ]T) ≡ ᴱP A [ ᴱs σ ]T
[]Tᴱ {A = El a}   = refl
[]Tᴱ {A = Π̂P T A} = Π̂P T & ext λ τ → []Tᴱ {A = A τ}
[]Tᴱ {A = a ⇒P A} = _⇒P_ (ᴱt a [ ᴱs _ ]t) & []Tᴱ {A = A}
{-# REWRITE []Tᴱ #-}

[]Cᴱ : ∀{Γc Δc}{σ : Sub Γc Δc}{Δ : Con Δc}
       → ᴱC (Δ [ σ ]C) ≡ (ᴱC Δ [ ᴱs σ ]C)
[]Cᴱ {Δ = ∙}      = refl
[]Cᴱ {Δ = Δ ▶P A} = (λ Γᴱ → Γᴱ ▶P _) & []Cᴱ {Δ = Δ}
{-# REWRITE []Cᴱ #-}

vs,ᴱ : ∀{Γc B B'}{x : Tm Γc B} → ᴱt (vs{Γc}{B}{B'} x) ≡ vs (ᴱt x)
vs,ᴱ {x = var x}  = refl
vs,ᴱ {x = x $S τ} = vs,ᴱ {x = x}
{-# REWRITE vs,ᴱ #-}

wk,ᴱ : ∀{Γc Δc B}{σ : Sub Γc Δc} → ᴱs (wk {B = B} σ) ≡ wk (ᴱs σ)
wk,ᴱ {σ = ε}     = refl
wk,ᴱ {σ = σ , t} = (λ σ → σ , _) & wk,ᴱ {σ = σ}
{-# REWRITE wk,ᴱ #-}

idᴱ : ∀{Γc} → ᴱs {Γc = Γc} id ≡ id
idᴱ {∙c}      = refl
idᴱ {Γc ▶c B} = (λ σ → σ , vz) & (wk & idᴱ {Γc = Γc})
{-# REWRITE idᴱ #-}

∘ᴱ : ∀{Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}
     → ᴱs (σ ∘ δ) ≡ (ᴱs σ ∘ ᴱs δ)
∘ᴱ {σ = ε}     {δ} = refl
∘ᴱ {σ = σ , t} {δ} = (λ σᴱ → σᴱ , _) & ∘ᴱ {σ = σ} {δ}
{-# REWRITE ∘ᴱ #-}

π₁ᴱ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)} → ᴱs (π₁ σ) ≡ π₁ (ᴱs σ)
π₁ᴱ {σ = σ , t} = refl
{-# REWRITE π₁ᴱ #-}

π₂ᴱ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)} → ᴱt (π₂ σ) ≡ π₂ (ᴱs σ)
π₂ᴱ {σ = σ , x} = refl
{-# REWRITE π₂ᴱ #-}

ᴱtP : ∀{Γc}{Γ : Con Γc}{A} → TmP Γ A → TmP (ᴱC Γ) (ᴱP A)
ᴱtP (varP vvzP)     = varP vvzP
ᴱtP (varP (vvsP x)) = vsP (ᴱtP (varP x))
ᴱtP (tP $P sP)      = ᴱtP tP $P ᴱtP sP
ᴱtP (tP $̂P τ)       = ᴱtP tP $̂P τ

ᴱsP : ∀{Γc}{Γ Δ : Con Γc} → SubP Γ Δ → SubP (ᴱC Γ) (ᴱC Δ)
ᴱsP εP         = εP
ᴱsP (σP ,P tP) = ᴱsP σP ,P ᴱtP tP

vsP,ᴱ : ∀{Γc}{Γ : Con Γc}{A A'}{tP : TmP Γ A}
        → ᴱtP (vsP {A' = A'} tP) ≡ vsP (ᴱtP tP)
vsP,ᴱ {tP = varP x}   = refl
vsP,ᴱ {tP = tP $P sP} = _$P_ & vsP,ᴱ {tP = tP}
                        ⊗ vsP,ᴱ {tP = sP}
vsP,ᴱ {tP = tP $̂P τ}  = (λ tP → tP $̂P τ) & vsP,ᴱ {tP = tP}
{-# REWRITE vsP,ᴱ #-}

[]ᴱtP : ∀{Γc}{Γ Δ : Con Γc}{A}{tP : TmP Δ A}{σP : SubP Γ Δ}
        → ᴱtP (tP [ σP ]tP) ≡ ᴱtP tP [ ᴱsP σP ]tP
[]ᴱtP {tP = varP vvzP}     {σP ,P _} = refl
[]ᴱtP {tP = varP (vvsP x)} {σP ,P _} = []ᴱtP {tP = varP x} {σP}
[]ᴱtP {tP = tP $P sP}      {σP}      = _$P_ & []ᴱtP {tP = tP} {σP}
                                         ⊗ []ᴱtP {tP = sP} {σP}
[]ᴱtP {tP = tP $̂P τ}       {σP}      = (λ tP → tP $̂P τ)
                                         & []ᴱtP {tP = tP} {σP}
{-# REWRITE []ᴱtP #-}

wkP,ᴱ : ∀{Γc}{Γ Δ : Con Γc}{A}(σP : SubP Γ Δ)
        → ᴱsP (wkP {A = A} σP) ≡ wkP (ᴱsP σP)
wkP,ᴱ εP         = refl
wkP,ᴱ (σP ,P tP) = (λ x → x ,P _) & wkP,ᴱ σP
{-# REWRITE wkP,ᴱ #-}

idPᴱ : ∀{Γc}{Γ : Con Γc} → ᴱsP (idP {Γ = Γ}) ≡ idP
idPᴱ {Γ = ∙}      = refl
idPᴱ {Γ = Γ ▶P A} = (λ σP → wkP σP ,P vzP) & (idPᴱ {Γ = Γ})
{-# REWRITE idPᴱ #-}

--TODO complete substitution calculus
