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

[]Tᵃ : ∀{ℓ Γc Δc A}{σ : Sub Γc Δc} → (γc : _ᵃc {ℓ} Γc) → ((A [ σ ]T) ᵃP) γc ≡ (A ᵃP) ((σ ᵃs) γc)
[]tᵃ : ∀{ℓ Γc Δc B}{t : Tm Δc B}{σ : Sub Γc Δc} → (γc : _ᵃc {ℓ} Γc) → ((t [ σ ]t) ᵃt) γc ≡ (t ᵃt) ((σ ᵃs) γc)

[]Tᵃ {A = El a}   γc = []tᵃ {t = a} γc
[]Tᵃ {A = Π̂P T A} γc = Π≡ refl λ τ → []Tᵃ {A = A τ} γc
[]Tᵃ {A = a ⇒P A} γc = Π≡ ([]tᵃ {t = a} γc) λ α → []Tᵃ {A = A} γc

[]tᵃ {t = var vvz}    {σ , x} γc = refl
[]tᵃ {t = var (vvs a)}{σ , x} γc = []tᵃ {t = var a} γc
[]tᵃ {t = t $S α}     {σ}     γc = happly ([]tᵃ {t = t} γc) α
{-# REWRITE []Tᵃ #-}
{-# REWRITE []tᵃ #-}

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
▶Sᵃ : ∀{ℓ Γc}{Γ : Con Γc}{B γc T} → _ᵃC {ℓ} (Γ ▶S B) (γc , T) ≡ _ᵃC Γ γc
▶Sᵃ {Γ = ∙} = refl
▶Sᵃ {Γ = Γ ▶P B} = (λ A → A × (B ᵃP) _) & ▶Sᵃ {Γ = Γ}
{-# REWRITE ▶Sᵃ #-}

_ᵃtP : ∀{ℓ Γc}{Γ : Con Γc}{A}(tP : TmP Γ A){γc}(γ : _ᵃC {ℓ} Γ γc) → _ᵃP {ℓ} A γc
(varP vvzP ᵃtP)     (γ , α) = α
(varP (vvsP x) ᵃtP) (γ , α) = (varP x ᵃtP) γ
((tP $P sP) ᵃtP)    γ       = (tP ᵃtP) γ ((sP ᵃtP) γ)
((tP $̂P τ) ᵃtP)     γ       = (tP ᵃtP) γ τ

_ᵃsP : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ Δ}(σP : SubP σ Γ Δ){γc}
         → _ᵃC {ℓ} Γ γc → _ᵃC {ℓ} Δ ((σ ᵃs) γc)
(εP ᵃsP) γ         = lift tt
((σP ,P tP) ᵃsP) γ = (σP ᵃsP) γ , (tP ᵃtP) γ

vsP,ᵃ : ∀{ℓ Γc}{Γ : Con Γc}{A A'}{tP : TmP Γ A}{γc}{γ : (Γ ᵃC) γc}{α : _ᵃP {ℓ} A' γc}
          → (vsP {A' = A'} tP ᵃtP) {γc} (γ , α) ≡ (tP ᵃtP) γ
vsP,ᵃ {tP = varP x}   = refl
vsP,ᵃ {tP = tP $P sP} = vsP,ᵃ {tP = tP} ⊗ vsP,ᵃ {tP = sP}
vsP,ᵃ {tP = tP $̂P τ}  = happly (vsP,ᵃ {tP = tP}) τ
{-# REWRITE vsP,ᵃ #-}

wkP,ᵃ : ∀{ℓ Γc Δc}{Γ : Con Γc}{Δ : Con Δc}{A}{σ}(σP : SubP σ Γ Δ){γc}{γ : (Γ ᵃC) γc}
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

-- TODO LSub should have been made obsolete by the point substitutions
data LSub {ℓ Γc Δc}(σ : Sub Γc Δc)(Γ : Con Γc) : Con Δc → Set (suc ℓ) where
  Lε   : LSub σ Γ ∙
  _,P_ : ∀{Δ A} → LSub {ℓ} σ Γ Δ → (∀{γc} → _ᵃC {ℓ} Γ γc → (A ᵃP) ((σ ᵃs) γc)) → LSub σ Γ (Δ ▶P A)

_,SL_ : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ} → (σP : LSub {ℓ} σ Γ Δ) → {B : TyS} → (b : Tm Γc B) → LSub {ℓ} (σ , b) Γ (Δ ▶S B)
_,SL_ {Δ = ∙}      σP        b = Lε
_,SL_ {Δ = Δ ▶P B} (σP ,P α) b = (σP ,SL b) ,P α

_ᵃsL : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ : Con Γc}{Δ : Con Δc}(σP : LSub {ℓ} σ Γ Δ){γc : _ᵃc {ℓ} Γc} → (Γ ᵃC) γc → (Δ ᵃC) ((σ ᵃs) γc)
_ᵃsL Lε γ                            = lift tt
_ᵃsL (σP ,P α) γ                     = (σP ᵃsL) γ , α γ

,SᵃsL : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ}{Δ}{σP : LSub {ℓ} σ Γ Δ}{B}{b : Tm Γc B}{γc}{γ : _ᵃC {ℓ} Γ γc} → ((σP ,SL b) ᵃsL) γ ≡ (σP ᵃsL) γ
,SᵃsL {Δ = ∙} {Lε} = refl
,SᵃsL {Δ = Δ ▶P B} {σP ,P α} = ,≡ ,SᵃsL refl
{-# REWRITE ,SᵃsL #-}

Lπ₁S : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub {ℓ} σ Γ (Δ ▶S B)) → LSub {ℓ} (π₁ σ) Γ Δ
Lπ₁S {Δ = ∙} Lε = Lε
Lπ₁S {Δ = Δ ▶P B} (σP ,P α) = Lπ₁S σP ,P α

Lπ₁SᵃsL : ∀{ℓ Γc Δc Γ Δ B}{γc}{γ : _ᵃC {ℓ} Γ γc}{σ : Sub Γc (Δc ▶c B)}(σP : LSub σ Γ (Δ ▶S B)) → (Lπ₁S σP ᵃsL) γ ≡ (σP ᵃsL) γ
Lπ₁SᵃsL {Δ = ∙} Lε = refl
Lπ₁SᵃsL {Δ = Δ ▶P B} (σP ,P α) = ,≡ (Lπ₁SᵃsL σP) refl
{-# REWRITE Lπ₁SᵃsL #-}

Lπ₁P : ∀{ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ (Δ ▶P A)) → LSub {ℓ} σ Γ Δ
Lπ₁P (σP ,P α) = σP

Lπ₁PᵃsL : ∀{ℓ Γc Δc Γ Δ A}{γc}{γ : (Γ ᵃC) γc}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ (Δ ▶P A)) → (Lπ₁P σP ᵃsL) γ ≡ ₁ ((σP ᵃsL) γ)
Lπ₁PᵃsL (σP ,P α) = refl
{-# REWRITE Lπ₁PᵃsL #-}

Lπ₂S : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc (Δc ▶c B)}(σP : LSub {ℓ} σ Γ (Δ ▶S B)) → Tm Γc B
Lπ₂S {σ = σ , t} σP = t

LwkS : ∀{ℓ Γc Δc Γ Δ B}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ Δ) → LSub {ℓ} (wk σ) (Γ ▶S B) Δ
LwkS Lε = Lε
LwkS (σP ,P α) = LwkS σP ,P α

LwkSᵃsL : ∀{ℓ Γc Δc Γ Δ B}{γc}{γ : _ᵃC {ℓ} Γ γc}{β}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkS {B = B} σP ᵃsL) {γc , β} γ  ≡ (σP ᵃsL) γ
LwkSᵃsL Lε = refl
LwkSᵃsL (σP ,P α) = ,≡ (LwkSᵃsL σP) refl
{-# REWRITE LwkSᵃsL #-}

LwkP : ∀{ℓ Γc Δc Γ Δ A}{σ : Sub Γc Δc}(σP : LSub {ℓ} σ Γ Δ) → LSub {ℓ} σ (Γ ▶P A) Δ
LwkP Lε        = Lε
LwkP (σP ,P α) = LwkP σP ,P λ γ → α (₁ γ)

LwkPᵃsL : ∀{ℓ Γc Δc Γ Δ A}{γc}{γ : _ᵃC {ℓ} Γ γc}{α : (A ᵃP) γc}{σ : Sub Γc Δc} → (σP : LSub σ Γ Δ) → (LwkP {A = A} σP ᵃsL) (γ , α) ≡ (σP ᵃsL) γ
LwkPᵃsL Lε        = refl
LwkPᵃsL (σP ,P α) = ,≡ (LwkPᵃsL σP) refl
{-# REWRITE LwkPᵃsL #-}

Lid : ∀{ℓ Γc}{Γ : Con Γc} → LSub {ℓ} id Γ Γ
Lid {Γ = ∙}      = Lε
Lid {Γ = Γ ▶P A} = LwkP Lid ,P ₂

LidᵃsL : ∀{ℓ Γc}{Γ : Con Γc}{γc}{γ : _ᵃC {ℓ} Γ γc} → (Lid {Γ = Γ} ᵃsL) γ ≡ γ
LidᵃsL {Γ = ∙}      = refl
LidᵃsL {Γ = Γ ▶P A} = ,≡ (LidᵃsL {Γ = Γ}) refl
{-# REWRITE LidᵃsL #-}

_L∘_ : ∀{ℓ Γc Δc Ωc}{Γ Δ Ω}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub {ℓ} δ Ω Δ)(σP : LSub {ℓ} σ Γ Ω) → LSub {ℓ} (δ ∘ σ) Γ Δ
Lε L∘ σP                      = Lε
_L∘_ {δ = δ} {σ} (δP ,P α) σP = (δP L∘ σP) ,P λ γ → α ((σP ᵃsL) γ)

L∘ᵃsL : ∀{ℓ Γc Δc Ωc}{Γ Δ Ω}{γc}{γ : _ᵃC {ℓ} Γ γc}{δ : Sub Ωc Δc}{σ : Sub Γc Ωc}(δP : LSub δ Ω Δ)(σP : LSub σ Γ Ω)
        → ((δP L∘ σP) ᵃsL) γ ≡ (δP ᵃsL) ((σP ᵃsL) γ)
L∘ᵃsL Lε σP        = refl
L∘ᵃsL (δP ,P α) σP = ,≡ (L∘ᵃsL δP σP) refl
{-# REWRITE L∘ᵃsL #-}
