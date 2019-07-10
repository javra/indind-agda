{-# OPTIONS --rewriting --allow-unsolved-meta #-}
module IFD where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵈS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → Set (suc ℓ' ⊔ suc ℓ)
ᵈS {ℓ'}{ℓ} U       α = α → Set (ℓ' ⊔ ℓ)
ᵈS {ℓ'}   (Π̂S T B) π = (τ : T) → ᵈS {ℓ'} (B τ) (π τ)

ᵈc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵃc {ℓ} Γc) → Set (suc ℓ' ⊔ suc ℓ)
ᵈc      ∙c        γc       = Lift _ ⊤
ᵈc {ℓ'} (Γc ▶c B) (γc , α) = ᵈc {ℓ'} Γc γc × ᵈS {ℓ'} B α

ᵈt : ∀{ℓ' ℓ Γc B}(t : Tm Γc B){γc : _ᵃc {ℓ} Γc} → ᵈc {ℓ'} Γc γc → ᵈS {ℓ'} B ((t ᵃt) γc)
ᵈt (var vvz)     (γcᵈ , αᵈ) = αᵈ
ᵈt (var (vvs t)) (γcᵈ , αᵈ) = ᵈt (var t) γcᵈ
ᵈt (t $S α)      γcᵈ        = ᵈt t γcᵈ α

ᵈP : ∀{ℓ' ℓ Γc}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(α : (A ᵃP) γc) → Set (ℓ' ⊔ ℓ)
ᵈP {ℓ'}{ℓ} (El a)   γcᵈ α =  ᵈt a γcᵈ α
ᵈP {ℓ'}    (Π̂P T A) γcᵈ π = (τ : T) → ᵈP {ℓ'} (A τ) γcᵈ (π τ)
ᵈP {ℓ'}    (a ⇒P A) γcᵈ π = (α : (a ᵃt) _) (αᵈ : ᵈt a γcᵈ α) → ᵈP A γcᵈ (π α)

ᵈC : ∀{ℓ' ℓ Γc}(Γ : Con Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(γ : (Γ ᵃC) γc) → Set (suc ℓ' ⊔ ℓ)
ᵈC ∙        γcᵈ γ       = Lift _ ⊤
ᵈC (Γ ▶P A) γcᵈ (γ , α) = (ᵈC Γ γcᵈ γ) × (ᵈP A γcᵈ α)

ᵈs : ∀{ℓ' ℓ Γc Δc}(σ : Sub Γc Δc){γc} → ᵈc {ℓ'}{ℓ} Γc γc → ᵈc {ℓ'} Δc ((σ ᵃs) γc)
ᵈs ε       γcᵈ = lift tt
ᵈs (σ , t) γcᵈ = ᵈs σ γcᵈ , ᵈt t γcᵈ

[]tᵈ : ∀{ℓ' ℓ Γc Δc A}(a : Tm Δc A){σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}
         → ᵈt (a [ σ ]t) γcᵈ ≡ ᵈt a (ᵈs σ γcᵈ)
[]tᵈ (var vvz)     {σ , t} = refl
[]tᵈ (var (vvs a)) {σ , t} = []tᵈ (var a)
[]tᵈ (a $S α)      {σ}     = happly ([]tᵈ a {σ = σ}) α
{-# REWRITE []tᵈ #-}

[]Tᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(α : _)
         → ᵈP (A [ σ ]T) γcᵈ α ≡ ᵈP A (ᵈs σ γcᵈ) α
[]Tᵈ {A = Π̂P T x} π = Π≡ refl λ α → []Tᵈ {A = x α} (π α)
[]Tᵈ {A = El a}   α = refl
[]Tᵈ {A = t ⇒P A} π = Π≡ refl λ α → Π≡ refl λ τ → []Tᵈ {A = A} (π α)
{-# REWRITE []Tᵈ #-}

[]Cᵈ : ∀{ℓ' ℓ Γc Δc}{σ : Sub Γc Δc}{Δ : Con Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(α : _)
          → ᵈC (Δ [ σ ]C) γcᵈ α ≡ ᵈC Δ (ᵈs σ γcᵈ) α
[]Cᵈ {Δ = ∙} α      = refl
[]Cᵈ {Δ = Δ ▶P A} α = ×≡ ([]Cᵈ (₁ α)) refl
{-# REWRITE []Cᵈ #-}

vs,ᵈ : ∀{ℓ' ℓ Γc B B'}{x : Tm Γc B}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}{α}{αᵈ : ᵈS {ℓ'}{ℓ} B' α}
         → ᵈt (vs x) (γcᵈ , αᵈ) ≡ ᵈt x γcᵈ
vs,ᵈ {x = var x}  = refl
vs,ᵈ {x = x $S α} = happly (vs,ᵈ {x = x}) α
{-# REWRITE vs,ᵈ #-}

wk,ᵈ : ∀{ℓ' ℓ Γc Δc B}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}{α αᵈ}
         → ᵈs (wk {B = B} σ) {γc , α} (γcᵈ , αᵈ) ≡ ᵈs σ {γc} γcᵈ
wk,ᵈ {σ = ε}     = refl
wk,ᵈ {σ = σ , x} = ,≡ wk,ᵈ refl
{-# REWRITE wk,ᵈ #-}

idᵈ : ∀{ℓ' ℓ Γc γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈs id γcᵈ ≡ γcᵈ
idᵈ {Γc = ∙c}      = refl
idᵈ {Γc = Γc ▶c x} = ,≡ idᵈ refl
{-# REWRITE idᵈ #-}

∘ᵈ : ∀{ℓ' ℓ Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}
       → ᵈs (σ ∘ δ) γcᵈ ≡ ᵈs σ (ᵈs δ γcᵈ)
∘ᵈ {σ = ε}        = refl
∘ᵈ {σ = σ , t}{δ} = ,≡ (∘ᵈ {σ = σ}{δ = δ}) ([]tᵈ t {δ})
{-# REWRITE ∘ᵈ #-}

π₁ᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈs (π₁ σ) γcᵈ ≡ ₁ (ᵈs σ γcᵈ)
π₁ᵈ {σ = σ , x} = refl
{-# REWRITE π₁ᵈ #-}

π₂ᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}
        → ᵈt (π₂ σ) γcᵈ ≡ ₂ (ᵈs σ γcᵈ)
π₂ᵈ {σ = σ , x} = refl
{-# REWRITE π₂ᵈ #-}

ᵈtP : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{A}(tP : TmP Γ A){γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}{γ}
       → ᵈC {ℓ'}{ℓ} Γ γcᵈ γ → ᵈP {ℓ'}{ℓ} A γcᵈ ((tP ᵃtP) γ)
ᵈtP (varP vvzP)     (γᵈ , αᵈ) = αᵈ
ᵈtP (varP (vvsP x)) (γᵈ , αᵈ) = ᵈtP (varP x) γᵈ
ᵈtP (tP $P sP)      γᵈ        = ᵈtP tP γᵈ ((sP ᵃtP) _) (ᵈtP sP γᵈ)
ᵈtP (tP $̂P τ)       γᵈ        = ᵈtP tP γᵈ τ

ᵈsP : ∀{ℓ' ℓ Γc}{Γ Δ : Con Γc}(σP : SubP Γ Δ){γc}{γcᵈ : ᵈc Γc γc}{γ}
       → ᵈC {ℓ'}{ℓ} Γ γcᵈ γ → ᵈC {ℓ'}{ℓ} Δ γcᵈ ((σP ᵃsP) γ)
ᵈsP εP         γᵈ = lift tt
ᵈsP (σP ,P tP) γᵈ = ᵈsP σP γᵈ , ᵈtP tP γᵈ

[]ᵈtP : ∀{ℓ' ℓ Γc}{Γ Δ : Con Γc}{σP : SubP Γ Δ}
         {A}{tP : TmP Δ A}{γc}{γcᵈ : ᵈc Γc γc}{γ}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}
        → ᵈtP  (tP [ σP ]tP) γᵈ ≡ ᵈtP tP (ᵈsP σP γᵈ)
[]ᵈtP {σP = εP}       {tP = varP ()}
[]ᵈtP {σP = σP ,P sP} {tP = varP vvzP} = refl
[]ᵈtP {σP = σP ,P sP} {tP = varP (vvsP x)} = []ᵈtP {σP = σP} {tP = varP x}
[]ᵈtP {σP = σP} {tP = tP $P sP} {γ = γ} = happly ([]ᵈtP {tP = tP}) ((sP ᵃtP) ((σP ᵃsP) γ))
                                          ⊗ []ᵈtP {tP = sP}
[]ᵈtP {σP = σP} {tP = tP $̂P τ} = happly ([]ᵈtP {σP = σP} {tP = tP}) τ
{-# REWRITE []ᵈtP #-}

vsP,ᵈ : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{A A'}
         {γc}{γ}{α}{γcᵈ : ᵈc Γc γc}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}{αᵈ : ᵈP A' γcᵈ α}(tP : TmP Γ A)
         → ᵈtP (vsP {A' = A'} tP) (γᵈ , αᵈ) ≡ ᵈtP tP γᵈ
vsP,ᵈ (varP x)   = refl
vsP,ᵈ (tP $P sP) = happly (vsP,ᵈ tP) _ ⊗ vsP,ᵈ sP
vsP,ᵈ (tP $̂P τ)  = happly (vsP,ᵈ tP) τ
{-# REWRITE vsP,ᵈ #-}

wkP,ᵈ : ∀{ℓ' ℓ Γc}{Γ Δ : Con Γc}{A}(σP : SubP Γ Δ)
         {γc}{γcᵈ : ᵈc Γc γc}{γ}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}{α}{αᵈ : ᵈP A γcᵈ α}
         → ᵈsP (wkP {A = A} σP) (γᵈ , αᵈ) ≡ ᵈsP σP γᵈ
wkP,ᵈ εP        = refl
wkP,ᵈ (σP ,P x) = ,≡ (wkP,ᵈ σP) refl
{-# REWRITE wkP,ᵈ #-}

idPᵈ : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{γc}{γcᵈ : ᵈc Γc γc}{γ}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}
        → ᵈsP {ℓ'}{ℓ}{Γc}{Γ} idP γᵈ ≡ γᵈ
idPᵈ {Γ = ∙} {γᵈ = lift tt}      = refl
idPᵈ {Γ = Γ ▶P A} {γᵈ = γᵈ , αᵈ} = ,≡ (idPᵈ {Γ = Γ}) refl
{-# REWRITE idPᵈ #-}
