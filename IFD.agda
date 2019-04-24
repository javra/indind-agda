{-# OPTIONS --rewriting --allow-unsolved-meta #-}
module IFD where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵈS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → Set (suc ℓ' ⊔ ℓ)
ᵈS {ℓ'} U        α = α → Set ℓ'
ᵈS {ℓ'} (Π̂S T B) π = (τ : T) → ᵈS {ℓ'} (B τ) (π τ)

ᵈc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵃc {ℓ} Γc) → Set (suc ℓ' ⊔ ℓ)
ᵈc      ∙c        γc       = Lift _ ⊤
ᵈc {ℓ'} (Γc ▶c B) (γc , α) = ᵈc {ℓ'} Γc γc × ᵈS {ℓ'} B α

ᵈt : ∀{ℓ' ℓ Γc B}(t : Tm Γc B){γc : _ᵃc {ℓ} Γc} → ᵈc {ℓ'} Γc γc → ᵈS {ℓ'} B ((t ᵃt) γc)
ᵈt (var vvz)     (γcᵈ , αᵈ) = αᵈ
ᵈt (var (vvs t)) (γcᵈ , αᵈ) = ᵈt (var t) γcᵈ
ᵈt (t $S α)      γcᵈ        = ᵈt t γcᵈ α

ᵈP : ∀{ℓ' ℓ Γc}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(α : (A ᵃP) γc) → Set (ℓ' ⊔ ℓ)
ᵈP {ℓ'}{ℓ} (El a)   γcᵈ α = Lift (ℓ' ⊔ ℓ) (ᵈt a γcᵈ α)
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
--{-# REWRITE []tᵈ #-}

[]Tᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(α : _)
         → ᵈP (A [ σ ]T) γcᵈ α ≡ ᵈP A (ᵈs σ γcᵈ) α
[]Tᵈ {A = Π̂P T x} π = Π≡ refl λ α → []Tᵈ {A = x α} (π α)
[]Tᵈ {A = El a}   α = Lift _ & happly ([]tᵈ a) α
[]Tᵈ {A = t ⇒P A} π = Π≡ refl λ α → Π≡ (happly ([]tᵈ t) α) λ τ → []Tᵈ {A = A} (π α)
{-# REWRITE []Tᵈ #-}

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
ᵈtP (tP $P sP)      γᵈ        = ᵈtP tP γᵈ _ (lower (ᵈtP sP γᵈ))
ᵈtP (tP $̂P τ)       γᵈ        = ᵈtP tP γᵈ τ

ᵈsP : ∀{ℓ' ℓ Γc Δc}{Γ : Con Γc}{Δ : Con Δc}{σ}(σP : SubP σ Γ Δ){γc}{γcᵈ : ᵈc Γc γc}{γ}
       → ᵈC {ℓ'}{ℓ} Γ γcᵈ γ → ᵈC {ℓ'}{ℓ} Δ (ᵈs σ γcᵈ) ((σP ᵃsP) γ)
ᵈsP εP         γᵈ = lift tt
ᵈsP (σP ,P tP) γᵈ = ᵈsP σP γᵈ , ᵈtP tP γᵈ

vsP,ᵈ : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{A A'}
         {γc}{γ}{α}{γcᵈ : ᵈc Γc γc}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}{αᵈ : ᵈP A' γcᵈ α}(tP : TmP Γ A)
         → ᵈtP (vsP {A' = A'} tP) (γᵈ , αᵈ) ≡ ᵈtP tP γᵈ
vsP,ᵈ (varP x)   = refl
vsP,ᵈ (tP $P sP) = happly (vsP,ᵈ tP) _ ⊗ lower & vsP,ᵈ sP
vsP,ᵈ (tP $̂P τ)  = happly (vsP,ᵈ tP) τ
{-# REWRITE vsP,ᵈ #-}

wkP,ᵈ : ∀{ℓ' ℓ Γc Δc}{Γ : Con Γc}{Δ : Con Δc}{A}{σ}(σP : SubP σ Γ Δ)
         {γc}{γcᵈ : ᵈc Γc γc}{γ}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}{α}{αᵈ : ᵈP A γcᵈ α}
         → ᵈsP (wkP {A = A} σP) (γᵈ , αᵈ) ≡ ᵈsP σP γᵈ
wkP,ᵈ εP        = refl
wkP,ᵈ (σP ,P x) = ,≡ (wkP,ᵈ σP) refl
{-# REWRITE wkP,ᵈ #-}

idPᵈ : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{γc}{γcᵈ : ᵈc Γc γc}{γ}{γᵈ : ᵈC {ℓ'}{ℓ} Γ γcᵈ γ}
        → ᵈsP idP γᵈ ≡ γᵈ
idPᵈ {Γ = ∙} {γᵈ = lift tt}      = refl
idPᵈ {Γ = Γ ▶P A} {γᵈ = γᵈ , αᵈ} = ,≡ idPᵈ refl
{-# REWRITE idPᵈ #-}

--TODO this should also all be obsolete
data dLSub {ℓ' ℓ} : ∀{Γc Δc}(σ : Sub Γc Δc){Γ : Con Γc}{Δ : Con Δc}(σP : LSub {ℓ} σ Γ Δ) → Set (suc (ℓ' ⊔ ℓ)) where
  dLε   : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ : Con Γc} → dLSub σ {Γ = Γ} Lε
  _,dP_ : ∀{Γc Δc σ}{Γ : Con Γc}{Δ : Con Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP){A : TyP Δc}
          → {α : ∀{γc} → _ᵃC {ℓ} Γ γc → (A ᵃP) ((σ ᵃs) γc)}
          → (αᵈ : ∀{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γ : _ᵃC {ℓ} Γ γc) → ᵈC Γ γcᵈ γ → ᵈP A {(σ ᵃs) γc} (ᵈs σ γcᵈ) (α γ))
          → dLSub σ (_,P_ σP {A} α)

ᵈsL : ∀{ℓ' ℓ Γc Δc}{σ}{Γ : Con Γc}{Δ : Con Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP)
       {γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γ : (Γ ᵃC) γc)
        → ᵈC Γ γcᵈ γ → ᵈC Δ (ᵈs σ γcᵈ) ((σP ᵃsL) γ)
ᵈsL dLε          γ γᵈ = lift tt
ᵈsL (σdP ,dP αᵈ) γ γᵈ = ᵈsL σdP γ γᵈ , αᵈ γ γᵈ

dLπ₁P : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ (Δ ▶P A)}
         (σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} σ (Lπ₁P σP)
dLπ₁P (σdP ,dP αᵈ) = σdP

ᵈsLdLπ₁P : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ (Δ ▶P A)}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC Γ γcᵈ γ}
            → ᵈsL (dLπ₁P σdP) γ γᵈ ≡ ₁ (ᵈsL σdP γ γᵈ)
ᵈsLdLπ₁P (σdP ,dP αᵈ) = refl
{-# REWRITE ᵈsLdLπ₁P #-}

dLwkP : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}
         (σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} σ (LwkP {A = A} σP)
dLwkP dLε          = dLε
dLwkP (σdP ,dP αᵈ) = dLwkP σdP ,dP λ γ γᵈ → αᵈ (₁ γ) (₁ γᵈ)

ᵈsLdLwkP : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}{α : (A ᵃP) γc}{αᵈ : ᵈP A γcᵈ α}
            → ᵈsL (dLwkP {A = A} σdP) (γ , α) (γᵈ , αᵈ) ≡ ᵈsL σdP γ γᵈ
ᵈsLdLwkP dLε                              = refl
ᵈsLdLwkP (σdP ,dP αᵈ) {γᵈ = γᵈ}{αᵈ = αᵈ'} = ,≡ (ᵈsLdLwkP σdP {γᵈ = γᵈ}{αᵈ = αᵈ'}) refl
{-# REWRITE ᵈsLdLwkP #-}

dLid : ∀{ℓ' ℓ Γc}{Γ : Con Γc} → dLSub {ℓ'}{ℓ} id (Lid {Γ = Γ})
dLid {Γ = ∙}      = dLε
dLid {Γ = Γ ▶P x} = dLwkP dLid ,dP λ γ → ₂

ᵈsLdLid : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}
           → ᵈsL {ℓ'}{ℓ} (dLid {Γ = Γ}) γ γᵈ ≡ γᵈ
ᵈsLdLid {Γ = ∙}      = refl
ᵈsLdLid {Γ = Γ ▶P x} = ,≡ (ᵈsLdLid {Γ = Γ}) refl
{-# REWRITE ᵈsLdLid #-}

_dL∘_ : ∀{ℓ' ℓ Γc Δc Ωc Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}{δP : LSub {ℓ} δ Ω Δ}{σP : LSub {ℓ} σ Γ Ω}
         (δdP : dLSub {ℓ'}{ℓ} δ δP)(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'}{ℓ} (δ ∘ σ) (δP L∘ σP)
dLε dL∘ σdP = dLε
_dL∘_ {δP = δP}{σP} (δdP ,dP αᵈ) σdP = (δdP dL∘ σdP) ,dP λ γ γᵈ → αᵈ ((σP ᵃsL) γ) (ᵈsL σdP γ γᵈ)

ᵈsLdL∘ : ∀{ℓ' ℓ Γc Δc Ωc Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}{δP : LSub {ℓ} δ Ω Δ}{σP : LSub {ℓ} σ Γ Ω}
          (δdP : dLSub {ℓ'}{ℓ} δ δP)(σdP : dLSub {ℓ'}{ℓ} σ σP)
          {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}
          → ᵈsL (δdP dL∘ σdP) γ γᵈ ≡ ᵈsL δdP ((σP ᵃsL) γ) (ᵈsL σdP γ γᵈ)
ᵈsLdL∘ dLε          σdP = refl
ᵈsLdL∘ (δdP ,dP αᵈ) σdP = ,≡ (ᵈsLdL∘ δdP σdP) refl
{-# REWRITE ᵈsLdL∘ #-}

