{-# OPTIONS --rewriting #-}
module IFA where

open import Lib hiding (id; _∘_)
open import IF

_ᴬS : TyS → Set₁
U ᴬS      = Set
Π̂S T A ᴬS = (α : T) → (A α) ᴬS

_ᴬc : SCon → Set₁
∙c ᴬc       = Lift ⊤
(Γ ▶c A) ᴬc = Γ ᴬc × A ᴬS

_ᴬt : {Γ : SCon}{A : TyS} → Tm Γ A → Γ ᴬc → A ᴬS
(vz ᴬt) (γ , α)   = α
(vs t ᴬt) (γ , α) = (t ᴬt) γ
((t $S α) ᴬt) γ   = (t ᴬt) γ α

_ᴬP : {Γc : SCon} → TyP Γc → (γ : Γc ᴬc) → Set₁
(Π̂P T A ᴬP) γ   = (α : T) → ((A α) ᴬP) γ
(El a ᴬP) γ     = Lift ((a ᴬt) γ)
((a ⇒P B) ᴬP) γ = (a ᴬt) γ → (B ᴬP) γ

_ᴬC : {Γc : SCon} → Con Γc → Γc ᴬc → Set₁
(∙ ᴬC) γ              = Lift ⊤
((Γ ▶S A) ᴬC) (γ , _) = (Γ ᴬC) γ
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

π₁ᴬ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → ((π₁ σ) ᴬs) γc ≡ ₁ ((σ ᴬs) γc)
π₁ᴬ {σ = σ , x} = refl
{-# REWRITE π₁ᴬ #-}

π₂ᴬ : ∀{Γc Δc A}{σ : Sub Γc (Δc ▶c A)}{γc} → ((π₂ σ) ᴬt) γc ≡ ₂ ((σ ᴬs) γc)
π₂ᴬ {σ = σ , x} = refl
{-# REWRITE π₂ᴬ #-}


data LSub : ∀{Γc Δc} → (σ : Sub Γc Δc) → (Γ : Con Γc) → (Δ : Con Δc) → Set₁ where
  Lε   : ∀{Γc}{Γ : Con Γc} → LSub ε Γ ∙
  _,S_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub σ Γ Δ) → {B : TyS} → (b : Tm Γc B) → LSub (σ , b) Γ (Δ ▶S B)
  _,P_ : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub σ Γ Δ) → {A : TyP Δc} → (α : ∀{γc} → (Γ ᴬC) γc → (A ᴬP) ((σ ᴬs) γc))
            → LSub σ Γ (Δ ▶P A)

_ᴬsL : ∀{Γc Δc : SCon}{σ : Sub Γc Δc}{Γ : Con Γc}{Δ : Con Δc}(σP : LSub σ Γ Δ) → (γc : Γc ᴬc) → (Γ ᴬC) γc → (Δ ᴬC) ((σ ᴬs) γc)
_ᴬsL Lε γc γ                            = lift tt
_ᴬsL (_,S_ {σ = σ} σP b) γc γ           = (σP ᴬsL) γc γ
_ᴬsL (σP ,P α) γc γ                     = (σP ᴬsL) γc γ , α γ

Lπ₁S : ∀{Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → LSub (π₁ σ) Γ Δ
Lπ₁S (σP ,S b) = σP

Lπ₁SᴬsL : ∀{Γc Δc Γ Δ B}{γc}{γ : (Γ ᴬC) γc}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → (Lπ₁S σP ᴬsL) γc γ ≡ (σP ᴬsL) γc γ
Lπ₁SᴬsL (σP ,S b) = refl
{-# REWRITE Lπ₁SᴬsL #-}

Lπ₁P : ∀{Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub σ Γ (Δ ▶P A)) → LSub σ Γ Δ
Lπ₁P (σP ,P α) = σP

Lπ₁PᴬsL : ∀{Γc Δc Γ Δ A}{γc}{γ : (Γ ᴬC) γc}{σ : Sub Γc Δc}(σP : LSub σ Γ (Δ ▶P A)) → (Lπ₁P σP ᴬsL) γc γ ≡ ₁ ((σP ᴬsL) γc γ)
Lπ₁PᴬsL (σP ,P α) = refl
{-# REWRITE Lπ₁PᴬsL #-}

Lπ₂S : ∀{Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → Tm Γc B
Lπ₂S (σP ,S b) = b

LwkS : ∀{Γc Δc Γ Δ B}{σ : Sub Γc Δc}(σP : LSub σ Γ Δ) → LSub (wk σ) (Γ ▶S B) Δ
LwkS Lε        = Lε
LwkS (σP ,S b) = LwkS σP ,S vs b
LwkS (σP ,P α) = LwkS σP ,P λ γ → α γ

LwkSᴬsL : ∀{Γc Δc Γ Δ B}{γc}{γ : (Γ ᴬC) γc}{β}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkS {B = B} σP ᴬsL)(γc , β) γ  ≡ (σP ᴬsL) γc γ
LwkSᴬsL Lε        = refl
LwkSᴬsL (σP ,S b) = LwkSᴬsL σP
LwkSᴬsL (σP ,P α) = ,≡ (LwkSᴬsL σP) refl
{-# REWRITE LwkSᴬsL #-}

LwkP : ∀{Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub σ Γ Δ) → LSub σ (Γ ▶P A) Δ
LwkP Lε        = Lε
LwkP (σP ,S b) = LwkP σP ,S b
LwkP (σP ,P α) = LwkP σP ,P λ γ → α (₁ γ)

LwkPᴬsL : ∀{Γc Δc Γ Δ A}{γc}{γ : (Γ ᴬC) γc}{α : (A ᴬP) γc}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkP {A = A} σP ᴬsL) γc (γ , α) ≡ (σP ᴬsL) γc γ
LwkPᴬsL Lε        = refl
LwkPᴬsL (σP ,S b) = LwkPᴬsL σP
LwkPᴬsL (σP ,P α) = ,≡ (LwkPᴬsL σP) refl
{-# REWRITE LwkPᴬsL #-}

Lid : ∀{Γc}{Γ : Con Γc} → LSub id Γ Γ
Lid {Γ = ∙}      = Lε
Lid {Γ = Γ ▶S B} = LwkS Lid ,S vz
Lid {Γ = Γ ▶P A} = LwkP Lid ,P ₂

LidᴬsL : ∀{Γc}{Γ : Con Γc}{γc}{γ : (Γ ᴬC) γc} → (Lid {Γ = Γ} ᴬsL) γc γ ≡ γ
LidᴬsL {Γ = ∙}      = refl
LidᴬsL {Γ = Γ ▶S B} = LidᴬsL {Γ = Γ}
LidᴬsL {Γ = Γ ▶P A} = ,≡ (LidᴬsL {Γ = Γ}) refl
{-# REWRITE LidᴬsL #-}

_L∘_ : ∀{Γc Δc Ωc}{Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω) → LSub (δ ∘ σ) Γ Δ
Lε L∘ σP                      = Lε
_L∘_ {σ = σ} (δP ,S b) σP     = (δP L∘ σP) ,S (b [ σ ]t)
_L∘_ {δ = δ} {σ} (δP ,P α) σP = (δP L∘ σP) ,P λ γ → α ((σP ᴬsL) _ γ)

L∘ᴬsL : ∀{Γc Δc Ωc}{Γ Δ Ω}{γc}{γ : (Γ ᴬC) γc}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω)
        → ((δP L∘ σP) ᴬsL) γc γ ≡ (δP ᴬsL) _ ((σP ᴬsL) γc γ)
L∘ᴬsL Lε σP        = refl
L∘ᴬsL (δP ,S b) σP = L∘ᴬsL δP σP
L∘ᴬsL (δP ,P α) σP = ,≡ (L∘ᴬsL δP σP) refl
{-# REWRITE L∘ᴬsL #-}
