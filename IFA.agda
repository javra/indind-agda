{-# OPTIONS --rewriting #-}
module IFA where

open import Lib hiding (id; _∘_)
open import IF

_ᵃS : ∀{ℓ} → TyS → Set (suc ℓ)
_ᵃS {ℓ} U        = Set ℓ
_ᵃS {ℓ} (Π̂S T B) = (τ : T) → _ᵃS {ℓ} (B τ)

_ᵃc : ∀{ℓ} → SCon → Set (suc ℓ)
∙c ᵃc             = Lift _ ⊤
_ᵃc {ℓ} (Γc ▶c B) = (_ᵃc {ℓ} Γc) × _ᵃS {ℓ} B

_ᵃt : ∀{ℓ Γc B} → Tm Γc B → _ᵃc {ℓ} Γc → _ᵃS {ℓ} B
(var vvz ᵃt)     (γ , α) = α
(var (vvs t) ᵃt) (γ , α) = (var t ᵃt) γ
((t $S α) ᵃt)    γ       = (t ᵃt) γ α

_ᵃP : ∀{ℓ Γc} → TyP Γc → _ᵃc {ℓ} Γc → Set ℓ
(El a ᵃP)     γ = (a ᵃt) γ
(Π̂P T A ᵃP)   γ = (τ : T) → ((A τ) ᵃP) γ
((a ⇒P A) ᵃP) γ = (a ᵃt) γ → (A ᵃP) γ

_ᵃC : ∀{ℓ Γc} → Con Γc → _ᵃc {ℓ} Γc → Set (suc ℓ)
(∙ ᵃC)        γ = Lift _ ⊤
((Γ ▶P A) ᵃC) γ = (Γ ᵃC) γ × (A ᵃP) γ

_ᵃs : ∀{ℓ}{Γc Δc} → Sub Γc Δc → _ᵃc {ℓ} Γc → _ᵃc {ℓ} Δc
(ε ᵃs) γ       = lift tt
((σ , t) ᵃs) γ = (σ ᵃs) γ , (t ᵃt) γ

[]tᵃ : ∀{ℓ Γc Δc B}{t : Tm Δc B}{σ : Sub Γc Δc}
       → (γc : _ᵃc {ℓ} Γc) → ((t [ σ ]t) ᵃt) γc ≡ (t ᵃt) ((σ ᵃs) γc)
[]tᵃ {t = var vvz}    {σ , x} γc = refl
[]tᵃ {t = var (vvs a)}{σ , x} γc = []tᵃ {t = var a} γc
[]tᵃ {t = t $S α}     {σ}     γc = happly ([]tᵃ {t = t} γc) α
{-# REWRITE []tᵃ #-}

[]Tᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc Δc} → (γc : _ᵃc {ℓ} Γc) → ((A [ σ ]T) ᵃP) γc ≡ (A ᵃP) ((σ ᵃs) γc)
[]Tᵃ {A = El a}   γc = []tᵃ {t = a} γc
[]Tᵃ {A = Π̂P T A} γc = Π≡ refl λ τ → []Tᵃ {A = A τ} γc
[]Tᵃ {A = a ⇒P A} γc = Π≡ ([]tᵃ {t = a} γc) λ α → []Tᵃ {A = A} γc
{-# REWRITE []Tᵃ #-}

[]Cᵃ : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Δ : Con Δc}{γc : _ᵃc {ℓ} Γc} → ((Δ [ σ ]C) ᵃC) γc ≡ (Δ ᵃC) ((σ ᵃs) γc)
[]Cᵃ {Δ = ∙}      = refl
[]Cᵃ {Δ = Δ ▶P A} = ×≡ []Cᵃ refl
{-# REWRITE []Cᵃ #-}

vs,ᵃ : ∀{ℓ Γc B B'}{x : Tm Γc B}{γc}{α : _ᵃS {ℓ} B'} → (vs x ᵃt) (γc , α) ≡ (x ᵃt) γc
vs,ᵃ {x = var x}  = refl
vs,ᵃ {x = x $S α} = happly (vs,ᵃ {x = x}) α
{-# REWRITE vs,ᵃ #-}

wk,ᵃ : ∀{ℓ Γc Δc B γc}{α : B ᵃS}{σ : Sub Γc Δc} → _ᵃs {ℓ} (wk {B = B} σ) (γc , α) ≡ (σ ᵃs) γc
wk,ᵃ {σ = ε}     = refl
wk,ᵃ {σ = σ , x} = ,≡ wk,ᵃ refl
{-# REWRITE wk,ᵃ #-}

idᵃ : ∀{ℓ Γc} → (γc : _ᵃc {ℓ} Γc) → (id ᵃs) γc ≡ γc
idᵃ {ℓ}{∙c}      γc       = refl
idᵃ {ℓ}{Γc ▶c x} (γc , α) = ,≡ (idᵃ γc) refl
{-# REWRITE idᵃ #-}

∘ᵃ : ∀{ℓ Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc} → _ᵃs {ℓ} (σ ∘ δ) γc ≡ (σ ᵃs) ((δ ᵃs) γc)
∘ᵃ {σ = ε}                      = refl
∘ᵃ {σ = σ , t} {δ = δ}{γc = γc} = happly2 _,_ (∘ᵃ {σ = σ} {δ = δ}) ((t ᵃt) ((δ ᵃs) γc))
{-# REWRITE ∘ᵃ #-}

π₁ᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵃs {ℓ} (π₁ σ) γc ≡ ₁ ((σ ᵃs) γc)
π₁ᵃ {σ = σ , x} = refl
{-# REWRITE π₁ᵃ #-}

π₂ᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵃt {ℓ} (π₂ σ) γc ≡ ₂ ((σ ᵃs) γc)
π₂ᵃ {σ = σ , x} = refl
{-# REWRITE π₂ᵃ #-}
{-
Twkᵃ : ∀{ℓ Γc}{B A γc T} → _ᵃP {ℓ} (Twk {Γc = Γc}{B = B} A) (γc , T) ≡ _ᵃP A γc
Twkᵃ {A = El x}   = refl
Twkᵃ {A = Π̂P T B} = Π≡ refl λ τ → Twkᵃ {A = B τ}
Twkᵃ {A = a ⇒P A} = Π≡ refl λ α → Twkᵃ {A = A}
{-# REWRITE Twkᵃ #-}
-}

_ᵃtP : ∀{ℓ Γc}{Γ : Con Γc}{A}(tP : TmP Γ A){γc}(γ : _ᵃC {ℓ} Γ γc) → _ᵃP {ℓ} A γc
(varP vvzP ᵃtP)     (γ , α) = α
(varP (vvsP x) ᵃtP) (γ , α) = (varP x ᵃtP) γ
((tP $P sP) ᵃtP)    γ       = (tP ᵃtP) γ ((sP ᵃtP) γ)
((tP $̂P τ) ᵃtP)     γ       = (tP ᵃtP) γ τ    

_ᵃsP : ∀{ℓ Γc}{Γ Δ : Con Γc}(σP : SubP Γ Δ){γc}
         → _ᵃC {ℓ} Γ γc → _ᵃC {ℓ} Δ γc
(εP ᵃsP) γ         = lift tt
((σP ,P tP) ᵃsP) γ = (σP ᵃsP) γ , (tP ᵃtP) γ

[]ᵃtP : ∀{ℓ Γc}{Γ Δ : Con Γc}{A}{tP : TmP Δ A}{σP : SubP Γ Δ}{γc}(γ : _ᵃC {ℓ} Γ γc)
        → _ᵃtP (tP [ σP ]tP) γ ≡ (tP ᵃtP) ((σP ᵃsP) γ)
[]ᵃtP {tP = varP vvzP}     {σP ,P sP} γ = refl
[]ᵃtP {tP = varP (vvsP v)} {σP ,P sP} γ = []ᵃtP {tP = varP v} γ
[]ᵃtP {tP = tP $P sP}      {σP} γ       = []ᵃtP {tP = tP} {σP} γ
                                          ⊗ []ᵃtP {tP = sP} γ
[]ᵃtP {tP = tP $̂P τ} γ                  = happly ([]ᵃtP {tP = tP} γ) τ
{-# REWRITE []ᵃtP #-}

vsP,ᵃ : ∀{ℓ Γc}{Γ : Con Γc}{A A'}{tP : TmP Γ A}{γc}{γ : (Γ ᵃC) γc}{α : _ᵃP {ℓ} A' γc}
          → (vsP {A' = A'} tP ᵃtP) {γc} (γ , α) ≡ (tP ᵃtP) γ
vsP,ᵃ {tP = varP x}   = refl
vsP,ᵃ {tP = tP $P sP} = vsP,ᵃ {tP = tP} ⊗ vsP,ᵃ {tP = sP}
vsP,ᵃ {tP = tP $̂P τ}  = happly (vsP,ᵃ {tP = tP}) τ
{-# REWRITE vsP,ᵃ #-}

wkP,ᵃ : ∀{ℓ Γc}{Γ Δ : Con Γc}{A}(σP : SubP Γ Δ){γc}{γ : (Γ ᵃC) γc}
         {α : _ᵃP {ℓ} A γc} → _ᵃsP {ℓ} (wkP {A = A} σP) (γ , α) ≡ (σP ᵃsP) γ 
wkP,ᵃ εP         = refl
wkP,ᵃ (σP ,P tP) = ,≡ (wkP,ᵃ σP) refl
{-# REWRITE wkP,ᵃ #-}

idPᵃ : ∀{ℓ Γc}{Γ : Con Γc}{γc}(γ : _ᵃC {ℓ} Γ γc) → (idP {Γ = Γ} ᵃsP) γ ≡ γ
idPᵃ {Γ = ∙}      (lift tt) = refl
idPᵃ {Γ = Γ ▶P A} (γ , α)   = ,≡ (idPᵃ {Γ = Γ} γ) refl
{-# REWRITE idPᵃ #-}

{-∘Pᵃ : ∀{ℓ Γc Δc Σc}{Γ : Con Γc}{Δ : Con Δc}{Σ : Con Σc}
      {σ}{σP : SubP σ Δ Σ}{δ}{δP : SubP δ Γ Δ}{γc}{γ : _ᵃC {ℓ} Γ γc}
      → (σP ∘P δP ᵃsP) γ ≡ (σP ᵃsP) ((δP ᵃsP) γ)
∘Pᵃ = ?-}

--TODO define ∘Pᵃ, π₁Pᵃ, π₂Pᵃ
