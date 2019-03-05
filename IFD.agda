{-# OPTIONS --rewriting #-}
module IFD where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

ᵈS : ∀{ℓ' ℓ}(B : TyS)(α : _ᵃS {ℓ} B) → Set (suc ℓ' ⊔ ℓ)
ᵈS {ℓ'} U        α = α → Set ℓ'
ᵈS {ℓ'} (Π̂S T B) π = (α : T) → ᵈS {ℓ'} (B α) (π α)

ᵈc : ∀{ℓ' ℓ}(Γc : SCon)(γc : _ᵃc {ℓ} Γc) → Set (suc ℓ' ⊔ ℓ)
ᵈc ∙c             γc       = Lift ⊤
ᵈc {ℓ'} (Γc ▶c B) (γc , α) = ᵈc {ℓ'} Γc γc × ᵈS {ℓ'} B α

ᵈt : ∀{ℓ'}{ℓ}{Γc : SCon}{B : TyS}(t : Tm Γc B)(γc : _ᵃc {ℓ} Γc) → ᵈc {ℓ'} Γc γc → ᵈS {ℓ'} B ((t ᵃt) γc)
ᵈt vz       (γc , α) (γcᵈ , αᵈ) = αᵈ
ᵈt (vs t  ) (γc , α) (γcᵈ , αᴾ) = ᵈt t γc γcᵈ
ᵈt (t $S α) γc       γcᵈ        = ᵈt t γc γcᵈ α

ᵈP : ∀{ℓ' ℓ}{Γc}(A : TyP Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(α : (A ᵃP) γc) → Set (ℓ' ⊔ ℓ)
ᵈP {ℓ'}    (Π̂P T B)      γcᵈ π = (α : T) → ᵈP {ℓ'} (B α) γcᵈ (π α)
ᵈP {ℓ'}{ℓ} (El a)   {γc} γcᵈ α = Lift {_}{ℓ' ⊔ ℓ} (ᵈt a γc γcᵈ α)
ᵈP {ℓ'}    (t ⇒P A) {γc} γcᵈ π = (α : (t ᵃt) γc) (αᵈ : ᵈt t γc γcᵈ α) → ᵈP A γcᵈ (π α)

ᵈC : ∀{ℓ' ℓ}{Γc}(Γ : Con Γc){γc : _ᵃc {ℓ} Γc}(γcᵈ : ᵈc {ℓ'} Γc γc)(γ : (Γ ᵃC) γc) → Set (suc ℓ' ⊔ ℓ)
ᵈC      ∙        γcᵈ        γ       = Lift ⊤
ᵈC {ℓ'} (Γ ▶S B) (γcᵈ , αᵈ) γ       = ᵈC {ℓ'} Γ γcᵈ γ
ᵈC {ℓ'} (Γ ▶P A) γcᵈ        (γ , α) = (ᵈC Γ γcᵈ γ)× (ᵈP A γcᵈ α)

ᵈs : ∀{ℓ' ℓ Γc Δc}(σ : Sub Γc Δc)(γc : _ᵃc {ℓ} Γc) → ᵈc {ℓ'} Γc γc → ᵈc {ℓ'} Δc ((σ ᵃs) γc)
ᵈs ε       γc γcᵈ = lift tt
ᵈs (σ , t) γc γcᵈ = ᵈs σ γc γcᵈ , ᵈt t γc γcᵈ

[]Tᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(α : _) → ᵈP (A [ σ ]T) γcᵈ α ≡ ᵈP A (ᵈs σ γc γcᵈ) α
[]tᵈ : ∀{ℓ' ℓ Γc Δc A}{a : Tm Δc A}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈt (a [ σ ]t) γc γcᵈ ≡ ᵈt a ((σ ᵃs) γc) (ᵈs σ γc γcᵈ)

[]Tᵈ {A = Π̂P T x} π = Π≡ refl λ α → []Tᵈ {A = x α} (π α)
[]Tᵈ {A = El a} α   = Lift & happly ([]tᵈ {a = a}) α
[]Tᵈ {A = t ⇒P A} π = Π≡ refl λ α → Π≡ (happly ([]tᵈ {a = t}) α) λ τ → []Tᵈ {A = A} (π α)

[]tᵈ {a = vz}    {σ , t} = refl
[]tᵈ {a = vs a}  {σ , t} = []tᵈ {a = a}
[]tᵈ {a = a $S α}{σ}     = happly ([]tᵈ {a = a} {σ = σ}) α
{-# REWRITE []Tᵈ #-}
{-# REWRITE []tᵈ #-}

wk,ᵈ : ∀{ℓ' ℓ Γc Δc B}{σ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}{α αᵈ}  → ᵈs (wk {B = B} σ) (γc , α) (γcᵈ , αᵈ) ≡ ᵈs σ γc γcᵈ
wk,ᵈ {σ = ε}     = refl
wk,ᵈ {σ = σ , x} = ,≡ wk,ᵈ refl
{-# REWRITE wk,ᵈ #-}

idᵈ : ∀{ℓ' ℓ Γc γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈs id γc γcᵈ ≡ γcᵈ
idᵈ {Γc = ∙c}      = refl
idᵈ {Γc = Γc ▶c x} = ,≡ idᵈ refl
{-# REWRITE idᵈ #-}

∘ᵈ : ∀{ℓ' ℓ Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈs (σ ∘ δ) γc γcᵈ ≡ ᵈs σ _ (ᵈs δ γc γcᵈ)
∘ᵈ {σ = ε}        = refl
∘ᵈ {σ = σ , x}{δ} = ,≡ (∘ᵈ {σ = σ}{δ = δ}) refl
{-# REWRITE ∘ᵈ #-}

π₁ᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈs (π₁ σ) γc γcᵈ ≡ ₁ (ᵈs σ γc γcᵈ)
π₁ᵈ {σ = σ , x} = refl
{-# REWRITE π₁ᵈ #-}

π₂ᵈ : ∀{ℓ' ℓ Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc} → ᵈt (π₂ σ) γc γcᵈ ≡ ₂ (ᵈs σ γc γcᵈ)
π₂ᵈ {σ = σ , x} = refl
{-# REWRITE π₂ᵈ #-}

data dLSub {ℓ' ℓ} : ∀{Γc Δc}(σ : Sub Γc Δc){Γ : Con Γc}{Δ : Con Δc}(σP : LSub {ℓ} σ Γ Δ) → Set (suc (ℓ' ⊔ ℓ)) where
  dLε   : ∀{Γc}{Γ : Con Γc} → dLSub ε {Γ = Γ} Lε
  _,dS_ : ∀{Γc Δc σ}{Γ : Con Γc}{Δ : Con Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP){B}(b : Tm Γc B) → dLSub (σ , b) (σP ,S b)
  _,dP_ : ∀{Γc Δc σ}{Γ : Con Γc}{Δ : Con Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP){A : TyP Δc}
          → {α : ∀{γc} → _ᵃC {ℓ} Γ γc → (A ᵃP) ((σ ᵃs) γc)}
          → (αᵈ : ∀{γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γ : _ᵃC {ℓ} Γ γc) → ᵈC Γ γcᵈ γ → ᵈP A {(σ ᵃs) γc} (ᵈs σ γc γcᵈ) (α γ))
          → dLSub σ (_,P_ σP {A} α)

ᵈsL : ∀{ℓ' ℓ Γc Δc}{σ}{Γ : Con Γc}{Δ : Con Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP){γc}{γcᵈ : ᵈc {ℓ'}{ℓ} Γc γc}(γ : (Γ ᵃC) γc)
      → ᵈC Γ γcᵈ γ → ᵈC Δ (ᵈs σ γc γcᵈ) ((σP ᵃsL) γ)
ᵈsL dLε          γ γᵈ = lift tt
ᵈsL (σdP ,dS b)  γ γᵈ = ᵈsL σdP γ γᵈ
ᵈsL (σdP ,dP αᵈ) γ γᵈ = ᵈsL σdP γ γᵈ , αᵈ γ γᵈ

dLπ₁S : ∀{ℓ' ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}{σP : LSub σ Γ (Δ ▶S B)}(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} (π₁ σ) (Lπ₁S σP)
dLπ₁S (σdP ,dS b) = σdP

ᵈsLdLπ₁S : ∀{ℓ' ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}{σP : LSub σ Γ (Δ ▶S B)}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC Γ γcᵈ γ}
            → ᵈsL (dLπ₁S σdP) γ γᵈ ≡ ᵈsL σdP γ γᵈ
ᵈsLdLπ₁S (σdP ,dS b) = refl
{-# REWRITE ᵈsLdLπ₁S #-}

dLπ₁P : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ (Δ ▶P A)}(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} σ (Lπ₁P σP)
dLπ₁P (σdP ,dP αᵈ) = σdP

ᵈsLdLπ₁P : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ (Δ ▶P A)}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC Γ γcᵈ γ}
            → ᵈsL (dLπ₁P σdP) γ γᵈ ≡ ₁ (ᵈsL σdP γ γᵈ)
ᵈsLdLπ₁P (σdP ,dP αᵈ) = refl
{-# REWRITE ᵈsLdLπ₁P #-}

dLπ₂S : ∀{ℓ' ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}{σP : LSub σ Γ (Δ ▶S B)}(σdP : dLSub {ℓ'}{ℓ} σ σP) → Tm Γc B
dLπ₂S (σdP ,dS b) = b

dLwkS : ∀{ℓ' ℓ Γc Δc Γ Δ B}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} (wk {B = B} σ) (LwkS σP)
dLwkS dLε          = dLε
dLwkS (σdP ,dS b)  = dLwkS σdP ,dS vs b
dLwkS (σdP ,dP αᵈ) = dLwkS σdP ,dP λ γ → αᵈ γ

ᵈsLdLwkS : ∀{ℓ' ℓ Γc Δc Γ Δ B}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}{β : B ᵃS}{βᵈ : ᵈS B β}
            → ᵈsL (dLwkS {B = B} σdP) {γc , β} {γcᵈ , βᵈ} γ γᵈ ≡ ᵈsL σdP γ γᵈ
ᵈsLdLwkS dLε                    = refl
ᵈsLdLwkS (σdP ,dS b)  {γᵈ = γᵈ} = ᵈsLdLwkS σdP {γᵈ = γᵈ}
ᵈsLdLwkS (σdP ,dP αᵈ) {γᵈ = γᵈ} = ,≡ (ᵈsLdLwkS σdP {γᵈ = γᵈ}) refl
{-# REWRITE ᵈsLdLwkS #-}

dLwkP : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'} σ (LwkP {A = A} σP)
dLwkP dLε          = dLε
dLwkP (σdP ,dS b)  = dLwkP σdP ,dS b
dLwkP (σdP ,dP αᵈ) = dLwkP σdP ,dP λ γ γᵈ → αᵈ (₁ γ) (₁ γᵈ)

ᵈsLdLwkP : ∀{ℓ' ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}{σP : LSub σ Γ Δ}(σdP : dLSub {ℓ'}{ℓ} σ σP)
            {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}{α : (A ᵃP) γc}{αᵈ : ᵈP A γcᵈ α}
            → ᵈsL (dLwkP {A = A} σdP) (γ , α) (γᵈ , αᵈ) ≡ ᵈsL σdP γ γᵈ
ᵈsLdLwkP dLε                              = refl
ᵈsLdLwkP (σdP ,dS b)  {γᵈ = γᵈ}{αᵈ = αᵈ}  = ᵈsLdLwkP σdP {γᵈ = γᵈ}{αᵈ = αᵈ}
ᵈsLdLwkP (σdP ,dP αᵈ) {γᵈ = γᵈ}{αᵈ = αᵈ'} = ,≡ (ᵈsLdLwkP σdP {γᵈ = γᵈ}{αᵈ = αᵈ'}) refl
{-# REWRITE ᵈsLdLwkP #-}

dLid : ∀{ℓ' ℓ Γc}{Γ : Con Γc} → dLSub {ℓ'}{ℓ} id (Lid {Γ = Γ})
dLid {Γ = ∙}      = dLε
dLid {Γ = Γ ▶S A} = dLwkS dLid ,dS vz
dLid {Γ = Γ ▶P x} = dLwkP dLid ,dP λ γ → ₂

ᵈsLdLid : ∀{ℓ' ℓ Γc}{Γ : Con Γc}{γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}
           → ᵈsL {ℓ'}{ℓ} (dLid {Γ = Γ}) γ γᵈ ≡ γᵈ
ᵈsLdLid {Γ = ∙}      = refl
ᵈsLdLid {Γ = Γ ▶S A} = ᵈsLdLid {Γ = Γ}
ᵈsLdLid {Γ = Γ ▶P x} = ,≡ (ᵈsLdLid {Γ = Γ}) refl
{-# REWRITE ᵈsLdLid #-}

_dL∘_ : ∀{ℓ' ℓ Γc Δc Ωc Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}{δP : LSub {ℓ} δ Ω Δ}{σP : LSub {ℓ} σ Γ Ω}
         (δdP : dLSub {ℓ'}{ℓ} δ δP)(σdP : dLSub {ℓ'}{ℓ} σ σP) → dLSub {ℓ'}{ℓ} (δ ∘ σ) (δP L∘ σP)
dLε dL∘ σdP = dLε
_dL∘_ {σ = σ}       (δdP ,dS b)  σdP = (δdP dL∘ σdP) ,dS (b [ σ ]t)
_dL∘_ {δP = δP}{σP} (δdP ,dP αᵈ) σdP = (δdP dL∘ σdP) ,dP λ γ γᵈ → αᵈ ((σP ᵃsL) γ) (ᵈsL σdP γ γᵈ)

ᵈsLdL∘ : ∀{ℓ' ℓ Γc Δc Ωc Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}{δP : LSub {ℓ} δ Ω Δ}{σP : LSub {ℓ} σ Γ Ω}
          (δdP : dLSub {ℓ'}{ℓ} δ δP)(σdP : dLSub {ℓ'}{ℓ} σ σP)
          {γc γcᵈ}{γ : (Γ ᵃC) γc}{γᵈ : ᵈC {ℓ'} Γ γcᵈ γ}
          → ᵈsL (δdP dL∘ σdP) γ γᵈ ≡ ᵈsL δdP ((σP ᵃsL) γ) (ᵈsL σdP γ γᵈ)
ᵈsLdL∘ dLε          σdP = refl
ᵈsLdL∘ (δdP ,dS b)  σdP = ᵈsLdL∘ δdP σdP
ᵈsLdL∘ (δdP ,dP αᵈ) σdP = ,≡ (ᵈsLdL∘ δdP σdP) refl
{-# REWRITE ᵈsLdL∘ #-}
