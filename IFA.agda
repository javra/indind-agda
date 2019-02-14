{-# OPTIONS --rewriting #-}
module IFA where

open import Lib hiding (id; _∘_)
open import IF

_ᵃS : TyS → Set₁
U ᵃS      = Set
Π̂S T A ᵃS = (α : T) → (A α) ᵃS

_ᵃc : SCon → Set₁
∙c ᵃc       = Lift ⊤
(Γ ▶c A) ᵃc = Γ ᵃc × A ᵃS

_ᵃt : {Γ : SCon}{A : TyS} → Tm Γ A → Γ ᵃc → A ᵃS
(vz ᵃt) (γ , α)   = α
(vs t ᵃt) (γ , α) = (t ᵃt) γ
((t $S α) ᵃt) γ   = (t ᵃt) γ α

_ᵃP : {Γc : SCon} → TyP Γc → (γ : Γc ᵃc) → Set₁
(Π̂P T A ᵃP) γ   = (α : T) → ((A α) ᵃP) γ
(El a ᵃP) γ     = Lift ((a ᵃt) γ)
((a ⇒P B) ᵃP) γ = (a ᵃt) γ → (B ᵃP) γ

_ᵃC : {Γc : SCon} → Con Γc → Γc ᵃc → Set₁
(∙ ᵃC) γ              = Lift ⊤
((Γ ▶S A) ᵃC) (γ , _) = (Γ ᵃC) γ
((Γ ▶P A) ᵃC) γ       = (Γ ᵃC) γ × (A ᵃP) γ

_ᵃs : {Γc Δc : SCon} → Sub Γc Δc → Γc ᵃc → Δc ᵃc
(ε ᵃs) γ       = lift tt
((σ , t) ᵃs) γ = (σ ᵃs) γ , (t ᵃt) γ

[]Tᵃ : ∀{Γc Δc A}{δ : Sub Γc Δc} → (γc : Γc ᵃc) → ((A [ δ ]T) ᵃP) γc ≡ (A ᵃP) ((δ ᵃs) γc)
[]tᵃ : ∀{Γc Δc A}{a : Tm Δc A}{δ : Sub Γc Δc} → (γc : Γc ᵃc) → ((a [ δ ]t) ᵃt) γc ≡ (a ᵃt) ((δ ᵃs) γc)

[]Tᵃ {A = Π̂P T x} γc = Π≡ refl λ α → []Tᵃ {A = x α} γc
[]Tᵃ {A = El x} γc   = Lift & []tᵃ {a = x} γc
[]Tᵃ {A = x ⇒P A} γc = Π≡ ([]tᵃ {a = x} γc) λ α → []Tᵃ {A = A} γc

[]tᵃ {a = vz} {δ , x} γc   = refl
[]tᵃ {a = vs a} {δ , x} γc = []tᵃ {a = a} γc
[]tᵃ {a = a $S α} {δ} γc   = (λ x → coe x (((a [ δ ]t) ᵃt) γc α)) & (const& ([]tᵃ {a = a} {δ = δ} γc) ⁻¹)
                             ◾ apd (λ f → f α) ([]tᵃ {a = a} {δ = δ} γc)
{-# REWRITE []Tᵃ #-}
{-# REWRITE []tᵃ #-}

wk,ᵃ : ∀{Γc Δc B γc α} → {σ : Sub Γc Δc} → ((wk {B = B} σ) ᵃs) (γc , α) ≡ (σ ᵃs) γc
wk,ᵃ {σ = ε}     = refl
wk,ᵃ {σ = σ , x} = ,≡ wk,ᵃ refl
{-# REWRITE wk,ᵃ #-}

idᵃ : ∀{Γc} → (γc : Γc ᵃc) → (id ᵃs) γc ≡ γc
idᵃ {∙c} γc            = refl
idᵃ {Γc ▶c x} (γc , α) = ,≡ (idᵃ γc) refl
{-# REWRITE idᵃ #-}

∘ᵃ : ∀{Γc Δc Σc}{σ : Sub Δc Σc}{δ : Sub Γc Δc}{γc} → ((σ ∘ δ) ᵃs) (γc) ≡ (σ ᵃs) ((δ ᵃs) γc)
∘ᵃ {σ = ε}                      = refl
∘ᵃ {σ = σ , x} {δ = δ}{γc = γc} = happly2 _,_ (∘ᵃ {σ = σ} {δ = δ}) ((x ᵃt) ((δ ᵃs) γc))
{-# REWRITE ∘ᵃ #-}

π₁ᵃ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → ((π₁ σ) ᵃs) γc ≡ ₁ ((σ ᵃs) γc)
π₁ᵃ {σ = σ , x} = refl
{-# REWRITE π₁ᵃ #-}

π₂ᵃ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → ((π₂ σ) ᵃt) γc ≡ ₂ ((σ ᵃs) γc)
π₂ᵃ {σ = σ , x} = refl
{-# REWRITE π₂ᵃ #-}


data LSub : ∀{Γc Δc} → (σ : Sub Γc Δc) → (Γ : Con Γc) → (Δ : Con Δc) → Set₁ where
  Lε   : ∀{Γc}{Γ : Con Γc} → LSub ε Γ ∙
  _,S_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub σ Γ Δ) → {B : TyS} → (b : Tm Γc B) → LSub (σ , b) Γ (Δ ▶S B)
  _,P_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub σ Γ Δ) → {A : TyP Δc} → (α : ∀{γc} → (Γ ᵃC) γc → (A ᵃP) ((σ ᵃs) γc))
            → LSub σ Γ (Δ ▶P A)

_ᵃsL : ∀{Γc Δc : SCon}{σ : Sub Γc Δc}{Γ : Con Γc}{Δ : Con Δc}(σP : LSub σ Γ Δ) → (γc : Γc ᵃc) → (Γ ᵃC) γc → (Δ ᵃC) ((σ ᵃs) γc)
_ᵃsL Lε γc γ                            = lift tt
_ᵃsL (_,S_ {σ = σ} σP b) γc γ           = (σP ᵃsL) γc γ
_ᵃsL (σP ,P α) γc γ                     = (σP ᵃsL) γc γ , α γ

Lπ₁S : ∀{Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → LSub (π₁ σ) Γ Δ
Lπ₁S (σP ,S b) = σP

Lπ₁SᵃsL : ∀{Γc Δc Γ Δ B}{γc}{γ : (Γ ᵃC) γc}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → (Lπ₁S σP ᵃsL) γc γ ≡ (σP ᵃsL) γc γ
Lπ₁SᵃsL (σP ,S b) = refl
{-# REWRITE Lπ₁SᵃsL #-}

Lπ₁P : ∀{Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub σ Γ (Δ ▶P A)) → LSub σ Γ Δ
Lπ₁P (σP ,P α) = σP

Lπ₁PᵃsL : ∀{Γc Δc Γ Δ A}{γc}{γ : (Γ ᵃC) γc}{σ : Sub Γc Δc}(σP : LSub σ Γ (Δ ▶P A)) → (Lπ₁P σP ᵃsL) γc γ ≡ ₁ ((σP ᵃsL) γc γ)
Lπ₁PᵃsL (σP ,P α) = refl
{-# REWRITE Lπ₁PᵃsL #-}

Lπ₂S : ∀{Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → Tm Γc B
Lπ₂S (σP ,S b) = b

LwkS : ∀{Γc Δc Γ Δ B}{σ : Sub Γc Δc}(σP : LSub σ Γ Δ) → LSub (wk σ) (Γ ▶S B) Δ
LwkS Lε        = Lε
LwkS (σP ,S b) = LwkS σP ,S vs b
LwkS (σP ,P α) = LwkS σP ,P λ γ → α γ

LwkSᵃsL : ∀{Γc Δc Γ Δ B}{γc}{γ : (Γ ᵃC) γc}{β}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkS {B = B} σP ᵃsL)(γc , β) γ  ≡ (σP ᵃsL) γc γ
LwkSᵃsL Lε        = refl
LwkSᵃsL (σP ,S b) = LwkSᵃsL σP
LwkSᵃsL (σP ,P α) = ,≡ (LwkSᵃsL σP) refl
{-# REWRITE LwkSᵃsL #-}

LwkP : ∀{Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub σ Γ Δ) → LSub σ (Γ ▶P A) Δ
LwkP Lε        = Lε
LwkP (σP ,S b) = LwkP σP ,S b
LwkP (σP ,P α) = LwkP σP ,P λ γ → α (₁ γ)

LwkPᵃsL : ∀{Γc Δc Γ Δ A}{γc}{γ : (Γ ᵃC) γc}{α : (A ᵃP) γc}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkP {A = A} σP ᵃsL) γc (γ , α) ≡ (σP ᵃsL) γc γ
LwkPᵃsL Lε        = refl
LwkPᵃsL (σP ,S b) = LwkPᵃsL σP
LwkPᵃsL (σP ,P α) = ,≡ (LwkPᵃsL σP) refl
{-# REWRITE LwkPᵃsL #-}

Lid : ∀{Γc}{Γ : Con Γc} → LSub id Γ Γ
Lid {Γ = ∙}      = Lε
Lid {Γ = Γ ▶S B} = LwkS Lid ,S vz
Lid {Γ = Γ ▶P A} = LwkP Lid ,P ₂

LidᵃsL : ∀{Γc}{Γ : Con Γc}{γc}{γ : (Γ ᵃC) γc} → (Lid {Γ = Γ} ᵃsL) γc γ ≡ γ
LidᵃsL {Γ = ∙}      = refl
LidᵃsL {Γ = Γ ▶S B} = LidᵃsL {Γ = Γ}
LidᵃsL {Γ = Γ ▶P A} = ,≡ (LidᵃsL {Γ = Γ}) refl
{-# REWRITE LidᵃsL #-}

_L∘_ : ∀{Γc Δc Ωc}{Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω) → LSub (δ ∘ σ) Γ Δ
Lε L∘ σP                      = Lε
_L∘_ {σ = σ} (δP ,S b) σP     = (δP L∘ σP) ,S (b [ σ ]t)
_L∘_ {δ = δ} {σ} (δP ,P α) σP = (δP L∘ σP) ,P λ γ → α ((σP ᵃsL) _ γ)

L∘ᵃsL : ∀{Γc Δc Ωc}{Γ Δ Ω}{γc}{γ : (Γ ᵃC) γc}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω)
        → ((δP L∘ σP) ᵃsL) γc γ ≡ (δP ᵃsL) _ ((σP ᵃsL) γc γ)
L∘ᵃsL Lε σP        = refl
L∘ᵃsL (δP ,S b) σP = L∘ᵃsL δP σP
L∘ᵃsL (δP ,P α) σP = ,≡ (L∘ᵃsL δP σP) refl
{-# REWRITE L∘ᵃsL #-}
