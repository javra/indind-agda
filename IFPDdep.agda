{-# OPTIONS --prop --rewriting --allow-unsolved-meta #-}
module IFPDdep where

open import Lib hiding (id; _∘_)
open import StrictLib renaming (_,_ to _p,_)
open import IFdep
open import IFPAdep

ᵖᵈS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵖᵃS {ℓ} B) → Set (suc ℓ' ⊔ suc ℓ)
ᵖᵈS {ℓ'}{ℓ} U       α = α → Prop (ℓ' ⊔ ℓ)
ᵖᵈS {ℓ'}   (ΠS T B) π = (τ : T) → ᵖᵈS {ℓ'} (B τ) (π τ)

ᵖᵈc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵖᵃc {ℓ} Γc) → Set (suc ℓ' ⊔ suc ℓ)
ᵖᵈc      ∙c        γc       = Lift _ ⊤
ᵖᵈc {ℓ'} (Γc ▶c B) (γc , α)  = ᵖᵈc {ℓ'} Γc γc × ᵖᵈS {ℓ'} B α

ᵖᵈt : ∀{ℓ' ℓ Γc B}(t : Tm Γc B){γc : _ᵖᵃc {ℓ} Γc} → ᵖᵈc {ℓ'} Γc γc → ᵖᵈS {ℓ'} B ((t ᵖᵃt) γc)
ᵖᵈt (var vvz)     (γcᵈ , αᵈ) = αᵈ
ᵖᵈt (var (vvs t)) (γcᵈ , αᵈ) = ᵖᵈt (var t) γcᵈ
ᵖᵈt (t $S α)      γcᵈ        = ᵖᵈt t γcᵈ α

ᵖᵈP : ∀{ℓ' ℓ Γc}(A : TyP Γc){γc : _ᵖᵃc {ℓ} Γc}(γcᵈ : ᵖᵈc {ℓ'} Γc γc)(α : (A ᵖᵃP) γc) → Prop (ℓ' ⊔ ℓ)
ᵖᵈP {ℓ'}{ℓ} (El a)   γcᵈ α =  ᵖᵈt a γcᵈ α
ᵖᵈP {ℓ'}    (Π^P T A) γcᵈ π = (τ : T) → ᵖᵈP {ℓ'} (A τ) γcᵈ (π τ)
ᵖᵈP {ℓ'}    (a ⇒P A) γcᵈ π = (α : (a ᵖᵃt) _) (αᵈ : ᵖᵈt a γcᵈ α) → ᵖᵈP A γcᵈ (π α)

ᵖᵈC : ∀{ℓ' ℓ Γc}(Γ : Con Γc){γc : _ᵖᵃc {ℓ} Γc}(γcᵈ : ᵖᵈc {ℓ'} Γc γc)(γ : (Γ ᵖᵃC) γc) → Prop (ℓ' ⊔ ℓ)
ᵖᵈC ∙        γcᵈ γ        = P⊤
ᵖᵈC (Γ ▶P A) γcᵈ γ = (ᵖᵈC Γ γcᵈ (p₁ γ)) ∧ (ᵖᵈP A γcᵈ (p₂ γ))

ᵖᵈs : ∀{ℓ' ℓ Γc Δc}(σ : Sub Γc Δc){γc} → ᵖᵈc {ℓ'}{ℓ} Γc γc → ᵖᵈc {ℓ'} Δc ((σ ᵖᵃs) γc)
ᵖᵈs ε       γcᵈ = lift tt
ᵖᵈs (σ , t) γcᵈ = ᵖᵈs σ γcᵈ , ᵖᵈt t γcᵈ

[]tᵈ : ∀{ℓ' ℓ Γc Δc A}(a : Tm Δc A){σ : Sub Γc Δc}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}
         → ᵖᵈt (a [ σ ]t) γcᵈ ≡ ᵖᵈt a (ᵖᵈs σ γcᵈ)
[]tᵈ (var vvz)     {σ , t} = refl
[]tᵈ (var (vvs a)) {σ , t} = []tᵈ (var a)
[]tᵈ (a $S α)      {σ}     = happly ([]tᵈ a {σ = σ}) α
{-# REWRITE []tᵈ #-}

[]Tᵖᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}(α : _)
         → ᵖᵈP (A [ σ ]T) γcᵈ α ≡ ᵖᵈP A (ᵖᵈs σ γcᵈ) α
[]Tᵖᵈ {A = Π^P T A} π = ? --PΠ≡ refl λ α → []Tᵖᵈ {A = A α} (π α)
[]Tᵖᵈ {A = El a}    α = refl
[]Tᵖᵈ {A = t ⇒P A}{σ}{γc}{γcᵈ}  π = PPΠ≡ refl (λ α → (λ X → ᵖᵈt t (ᵖᵈs σ γcᵈ) α → X) & []Tᵖᵈ {A = A} {σ} {γc} {γcᵈ} (π α))
--{-# REWRITE []Tᵖᵈ #-}
{-
[]Cᵖᵈ : ∀{ℓ' ℓ Γc Δc}{σ : Sub Γc Δc}{Δ : Con Δc}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}(α : _)
          → ᵖᵈC (Δ [ σ ]C) γcᵈ α ≡ ᵖᵈC Δ (ᵖᵈs σ γcᵈ) α
[]Cᵖᵈ {Δ = ∙} α      = refl
[]Cᵖᵈ {Δ = Δ ▶P A} α = (λ p → p ∧ _) & []Cᵖᵈ (p₁ α)
{-# REWRITE []Cᵖᵈ #-}

vs,ᵖᵈ : ∀{ℓ' ℓ Γc B B'}{x : Tm Γc B}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}{α}{αᵈ : ᵖᵈS {ℓ'}{ℓ} B' α}
         → ᵖᵈt (vs x) (γcᵈ , αᵈ) ≡ ᵖᵈt x γcᵈ
vs,ᵖᵈ {x = var x}  = refl
vs,ᵖᵈ {x = x $S α} = happly (vs,ᵖᵈ {x = x}) α
{-# REWRITE vs,ᵖᵈ #-}

wk,ᵖᵈ : ∀{ℓ' ℓ Γc Δc B}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}{α αᵈ}
         → ᵖᵈs (wk {B = B} σ) {γc , α} (γcᵈ , αᵈ) ≡ ᵖᵈs σ {γc} γcᵈ
wk,ᵖᵈ {σ = ε}     = refl
wk,ᵖᵈ {σ = σ , x} = ,≡ wk,ᵖᵈ refl
{-# REWRITE wk,ᵖᵈ #-}

idᵖᵈ : ∀{ℓ' ℓ Γc γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc} → ᵖᵈs id γcᵈ ≡ γcᵈ
idᵖᵈ {Γc = ∙c}      = refl
idᵖᵈ {Γc = Γc ▶c x} {γc , α} {γcᵈ , αᵈ} = ,≡ idᵖᵈ refl
{-# REWRITE idᵖᵈ #-}

∘ᵖᵈ : ∀{ℓ' ℓ Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}
       → ᵖᵈs (σ ∘ δ) γcᵈ ≡ ᵖᵈs σ (ᵖᵈs δ γcᵈ)
∘ᵖᵈ {σ = ε}        = refl
∘ᵖᵈ {σ = σ , t}{δ} = ,≡ (∘ᵖᵈ {σ = σ}{δ = δ}) ([]tᵈ t {δ})
{-# REWRITE ∘ᵖᵈ #-}

π₁ᵖᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc} → ᵖᵈs (π₁ σ) γcᵈ ≡ ₁ (ᵖᵈs σ γcᵈ)
π₁ᵖᵈ {σ = σ , x} = refl
{-# REWRITE π₁ᵖᵈ #-}

π₂ᵖᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}
        → ᵖᵈt (π₂ σ) γcᵈ ≡ ₂ (ᵖᵈs σ γcᵈ)
π₂ᵖᵈ {σ = σ , x} = refl
{-# REWRITE π₂ᵖᵈ #-}

ᵖᵈtP : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{A}(tP : TmP Γ A){γc}{γcᵈ : ᵖᵈc {ℓ'}{ℓ} Γc γc}{γ}
       → ᵖᵈC {ℓ'}{ℓ} Γ γcᵈ γ → ᵖᵈP {ℓ'}{ℓ} A γcᵈ ((tP ᵖᵃtP) γ)
ᵖᵈtP (varP vvzP)             (γᵈ p, αᵈ) = αᵈ
ᵖᵈtP (varP (vvsP x))         (γᵈ p, αᵈ) = ᵖᵈtP (varP x) γᵈ
ᵖᵈtP (tP $P sP)      {γ = γ} γᵈ         = ᵖᵈtP tP γᵈ ((sP ᵖᵃtP) γ) (ᵖᵈtP sP γᵈ)
ᵖᵈtP (tP $^P τ)              γᵈ         = ᵖᵈtP tP γᵈ τ

ᵖᵈsP : ∀{ℓ' ℓ Γc}{Γ Δ : Con Γc}(σP : SubP Γ Δ){γc}{γcᵈ : ᵖᵈc Γc γc}{γ}
       → ᵖᵈC {ℓ'}{ℓ} Γ γcᵈ γ → ᵖᵈC {ℓ'}{ℓ} Δ γcᵈ ((σP ᵖᵃsP) γ)
ᵖᵈsP εP         γᵈ = ptt
ᵖᵈsP (σP ,P tP) γᵈ = ᵖᵈsP σP γᵈ p, ᵖᵈtP tP γᵈ

-}
