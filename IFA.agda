{-# OPTIONS --rewriting #-}
module IFA where

open import Lib hiding (id; _∘_)
open import IF

_ᵃS : ∀{ℓ} → TyS → Set (suc ℓ)
_ᵃS {ℓ} U        = Set ℓ
_ᵃS {ℓ} (Π̂S T A) = (α : T) → _ᵃS {ℓ} (A α)

_ᵃc : ∀{ℓ} → SCon → Set (suc ℓ)
∙c ᵃc            = Lift ⊤
_ᵃc {ℓ} (Γ ▶c A) = (_ᵃc {ℓ} Γ) × _ᵃS {ℓ} A

_ᵃt : ∀{ℓ}{Γ : SCon}{A : TyS} → Tm Γ A → _ᵃc {ℓ} Γ → _ᵃS {ℓ} A
(vz ᵃt) (γ , α)   = α
(vs t ᵃt) (γ , α) = (t ᵃt) γ
((t $S α) ᵃt) γ   = (t ᵃt) γ α

_ᵃP : ∀{ℓ}{Γc} → TyP Γc → (γ : _ᵃc {ℓ} Γc) → Set ℓ
(Π̂P T A ᵃP) γ   = (α : T) → ((A α) ᵃP) γ
(El a ᵃP) γ     = (a ᵃt) γ
((a ⇒P B) ᵃP) γ = (a ᵃt) γ → (B ᵃP) γ

_ᵃC : ∀{ℓ}{Γc} → Con Γc → _ᵃc {ℓ} Γc → Set (suc ℓ)
(∙ ᵃC) γ              = Lift ⊤
((Γ ▶S A) ᵃC) (γ , _) = (Γ ᵃC) γ
((Γ ▶P A) ᵃC) γ       = (Γ ᵃC) γ × (A ᵃP) γ

_ᵃs : ∀{ℓ}{Γc Δc} → Sub Γc Δc → _ᵃc {ℓ} Γc → _ᵃc {ℓ} Δc
(ε ᵃs) γ       = lift tt
((σ , t) ᵃs) γ = (σ ᵃs) γ , (t ᵃt) γ

[]Tᵃ : ∀{ℓ}{Γc Δc A}{δ : Sub Γc Δc} → (γc : _ᵃc {ℓ} Γc) → ((A [ δ ]T) ᵃP) γc ≡ (A ᵃP) ((δ ᵃs) γc)
[]tᵃ : ∀{ℓ}{Γc Δc A}{a : Tm Δc A}{δ : Sub Γc Δc} → (γc : _ᵃc {ℓ} Γc) → ((a [ δ ]t) ᵃt) γc ≡ (a ᵃt) ((δ ᵃs) γc)

[]Tᵃ {A = Π̂P T x} γc = Π≡ refl λ α → []Tᵃ {A = x α} γc
[]Tᵃ {A = El x} γc   = []tᵃ {a = x} γc
[]Tᵃ {A = x ⇒P A} γc = Π≡ ([]tᵃ {a = x} γc) λ α → []Tᵃ {A = A} γc

[]tᵃ {a = vz} {δ , x} γc   = refl
[]tᵃ {a = vs a} {δ , x} γc = []tᵃ {a = a} γc
[]tᵃ {a = a $S α} {δ} γc   = (λ x → coe x (((a [ δ ]t) ᵃt) γc α)) & (const& ([]tᵃ {a = a} {δ = δ} γc) ⁻¹)
                             ◾ apd (λ f → f α) ([]tᵃ {a = a} {δ = δ} γc)
{-# REWRITE []Tᵃ #-}
{-# REWRITE []tᵃ #-}

wk,ᵃ : ∀{ℓ}{Γc Δc B γc α} → {σ : Sub Γc Δc} → _ᵃs {ℓ} (wk {B = B} σ) (γc , α) ≡ (σ ᵃs) γc
wk,ᵃ {σ = ε}     = refl
wk,ᵃ {σ = σ , x} = ,≡ wk,ᵃ refl
{-# REWRITE wk,ᵃ #-}

idᵃ : ∀{ℓ}{Γc} → (γc : _ᵃc {ℓ} Γc) → (id ᵃs) γc ≡ γc
idᵃ {ℓ}{∙c} γc            = refl
idᵃ {ℓ}{Γc ▶c x} (γc , α) = ,≡ (idᵃ γc) refl
{-# REWRITE idᵃ #-}

∘ᵃ : ∀{ℓ}{Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc} → _ᵃs {ℓ} (σ ∘ δ) γc ≡ (σ ᵃs) ((δ ᵃs) γc)
∘ᵃ {σ = ε}                      = refl
∘ᵃ {σ = σ , x} {δ = δ}{γc = γc} = happly2 _,_ (∘ᵃ {σ = σ} {δ = δ}) ((x ᵃt) ((δ ᵃs) γc))
{-# REWRITE ∘ᵃ #-}

π₁ᵃ : ∀{ℓ}{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵃs {ℓ} (π₁ σ) γc ≡ ₁ ((σ ᵃs) γc)
π₁ᵃ {σ = σ , x} = refl
{-# REWRITE π₁ᵃ #-}

π₂ᵃ : ∀{ℓ}{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → _ᵃt {ℓ} (π₂ σ) γc ≡ ₂ ((σ ᵃs) γc)
π₂ᵃ {σ = σ , x} = refl
{-# REWRITE π₂ᵃ #-}

data LSub {ℓ} : ∀{Γc Δc} → (σ : Sub Γc Δc) → (Γ : Con Γc) → (Δ : Con Δc) → Set (suc ℓ) where
  Lε   : ∀{Γc}{Γ : Con Γc} → LSub ε Γ ∙
  _,S_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub {ℓ} σ Γ Δ) → {B : TyS} → (b : Tm Γc B) → LSub (σ , b) Γ (Δ ▶S B)
  _,P_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub {ℓ} σ Γ Δ) → {A : TyP Δc} → (α : ∀{γc} → _ᵃC {ℓ} Γ γc → (A ᵃP) ((σ ᵃs) γc))
            → LSub σ Γ (Δ ▶P A)

_ᵃsL : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ : Con Γc}{Δ : Con Δc}(σP : LSub {ℓ} σ Γ Δ){γc : _ᵃc {ℓ} Γc} → (Γ ᵃC) γc → (Δ ᵃC) ((σ ᵃs) γc)
_ᵃsL Lε γ                            = lift tt
_ᵃsL (_,S_ {σ = σ} σP b) γ           = (σP ᵃsL) γ
_ᵃsL (σP ,P α) γ                     = (σP ᵃsL) γ , α γ

Lπ₁S : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub {ℓ} σ Γ (Δ ▶S B)) → LSub {ℓ} (π₁ σ) Γ Δ
Lπ₁S (σP ,S b) = σP

Lπ₁SᵃsL : ∀{ℓ Γc Δc Γ Δ B}{γc}{γ : _ᵃC {ℓ} Γ γc}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → (Lπ₁S σP ᵃsL) γ ≡ (σP ᵃsL) γ
Lπ₁SᵃsL (σP ,S b) = refl
{-# REWRITE Lπ₁SᵃsL #-}

Lπ₁P : ∀{ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ (Δ ▶P A)) → LSub {ℓ} σ Γ Δ
Lπ₁P (σP ,P α) = σP

Lπ₁PᵃsL : ∀{ℓ Γc Δc Γ Δ A}{γc}{γ : (Γ ᵃC) γc}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ (Δ ▶P A)) → (Lπ₁P σP ᵃsL) γ ≡ ₁ ((σP ᵃsL) γ)
Lπ₁PᵃsL (σP ,P α) = refl
{-# REWRITE Lπ₁PᵃsL #-}

Lπ₂S : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub {ℓ} σ Γ (Δ ▶S B)) → Tm Γc B
Lπ₂S (σP ,S b) = b

LwkS : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ Δ) → LSub {ℓ} (wk σ) (Γ ▶S B) Δ
LwkS Lε        = Lε
LwkS (σP ,S b) = LwkS σP ,S vs b
LwkS (σP ,P α) = LwkS σP ,P λ γ → α γ

LwkSᵃsL : ∀{ℓ Γc Δc Γ Δ B}{γc}{γ : _ᵃC {ℓ} Γ γc}{β}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkS {B = B} σP ᵃsL) {γc , β} γ  ≡ (σP ᵃsL) γ
LwkSᵃsL Lε        = refl
LwkSᵃsL (σP ,S b) = LwkSᵃsL σP
LwkSᵃsL (σP ,P α) = ,≡ (LwkSᵃsL σP) refl
{-# REWRITE LwkSᵃsL #-}

LwkP : ∀{ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ Δ) → LSub {ℓ} σ (Γ ▶P A) Δ
LwkP Lε        = Lε
LwkP (σP ,S b) = LwkP σP ,S b
LwkP (σP ,P α) = LwkP σP ,P λ γ → α (₁ γ)

LwkPᵃsL : ∀{ℓ Γc Δc Γ Δ A}{γc}{γ : _ᵃC {ℓ} Γ γc}{α : (A ᵃP) γc}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkP {A = A} σP ᵃsL) (γ , α) ≡ (σP ᵃsL) γ
LwkPᵃsL Lε        = refl
LwkPᵃsL (σP ,S b) = LwkPᵃsL σP
LwkPᵃsL (σP ,P α) = ,≡ (LwkPᵃsL σP) refl
{-# REWRITE LwkPᵃsL #-}

Lid : ∀{ℓ Γc}{Γ : Con Γc} → LSub {ℓ} id Γ Γ
Lid {Γ = ∙}      = Lε
Lid {Γ = Γ ▶S B} = LwkS Lid ,S vz
Lid {Γ = Γ ▶P A} = LwkP Lid ,P ₂

LidᵃsL : ∀{ℓ Γc}{Γ : Con Γc}{γc}{γ : _ᵃC {ℓ} Γ γc} → (Lid {Γ = Γ} ᵃsL) γ ≡ γ
LidᵃsL {Γ = ∙}      = refl
LidᵃsL {Γ = Γ ▶S B} = LidᵃsL {Γ = Γ}
LidᵃsL {Γ = Γ ▶P A} = ,≡ (LidᵃsL {Γ = Γ}) refl
{-# REWRITE LidᵃsL #-}

_L∘_ : ∀{ℓ Γc Δc Ωc}{Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub {ℓ} δ Ω Δ)(σP : LSub {ℓ} σ Γ Ω) → LSub {ℓ} (δ ∘ σ) Γ Δ
Lε L∘ σP                      = Lε
_L∘_ {σ = σ} (δP ,S b) σP     = (δP L∘ σP) ,S (b [ σ ]t)
_L∘_ {δ = δ} {σ} (δP ,P α) σP = (δP L∘ σP) ,P λ γ → α ((σP ᵃsL) γ)

L∘ᵃsL : ∀{ℓ Γc Δc Ωc}{Γ Δ Ω}{γc}{γ : _ᵃC {ℓ} Γ γc}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω)
        → ((δP L∘ σP) ᵃsL) γ ≡ (δP ᵃsL) ((σP ᵃsL) γ)
L∘ᵃsL Lε σP        = refl
L∘ᵃsL (δP ,S b) σP = L∘ᵃsL δP σP
L∘ᵃsL (δP ,P α) σP = ,≡ (L∘ᵃsL δP σP) refl
{-# REWRITE L∘ᵃsL #-}
