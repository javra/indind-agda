{-# OPTIONS --rewriting #-}
module IFEx where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

data VarP {Γc} : Con Γc → TyP Γc → Set where
  vvPz : ∀{Γ A} → VarP (Γ ▶P A) A
  vvPs : ∀{Γ A B} → VarP Γ A → VarP (Γ ▶P B) A

data TmP {Γc}(Γ : Con Γc) : TyP Γc → Set₁ where
  varP : ∀{A} → VarP Γ A → TmP Γ A
  _$P_ : ∀{a A} → TmP Γ (a ⇒P A) → TmP Γ (El a) → TmP Γ A
  _$̂P_ : ∀{T A} → TmP Γ (Π̂P T A) → (τ : T) → TmP Γ (A τ)

data SubP {Γc Δc}(σ : Sub Γc Δc) : ∀(Γ : Con Γc)(Δ : Con Δc) → Set₁ where
  εP   : ∀{Γ} → SubP σ Γ ∙
  _,P_ : ∀{Γ Δ A} → SubP σ Γ Δ → TmP Γ (A [ σ ]T) → SubP σ Γ (Δ ▶P A)

vPz : ∀{Γc Γ A} → TmP {Γc} (Γ ▶P A) A
vPz = varP vvPz

vPs : ∀{Γc Γ A B} → TmP {Γc} Γ A → TmP (Γ ▶P B) A
vPs (varP x) = varP (vvPs x)
vPs (f $P t) = vPs f $P vPs t
vPs (f $̂P τ) = vPs f $̂P τ

wkP : ∀{Γc Δc}{σ : Sub Γc Δc}{Γ Δ A} → SubP σ Γ Δ → SubP σ (Γ ▶P A) Δ
wkP εP        = εP
wkP (σP ,P t) = wkP σP ,P vPs t

idP : ∀{Γc}{Γ : Con Γc} → SubP id Γ Γ
idP {Γ = ∙}      = εP
idP {Γ = Γ ▶P B} = wkP idP ,P vPz

conSᵃ' : ∀{Ωc}(Ω : Con Ωc){B}(t : Tm Ωc B) → _ᵃS {suc zero} B
conSᵃ' Ω {U}      t     = TmP Ω (El t)
conSᵃ' Ω {Π̂S T B} t     = λ τ → conSᵃ' Ω (t $S τ)

concᵃ' : ∀{Ωc}(Ω : Con Ωc)(Γc : SCon)(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
concᵃ' Ω ∙c        ε       = lift tt
concᵃ' Ω (Γc ▶c B) (σ , t) = concᵃ' Ω Γc σ , conSᵃ' Ω t

contᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → (t ᵃt) (concᵃ' Ω Γc σ) ≡ conSᵃ' Ω {B} (t [ σ ]t)
contᵃ' Ω            ε           t                   = ⊥-elim (Tm∙c t)
contᵃ' Ω            (σ , s)     (var vvz)           = refl
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (var (vvs x))       = contᵃ' Ω σ (var x)
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (_$S_ {T}{B''} t α) = happly (contᵃ' Ω (σ , s) {Π̂S T B''} t) α

conPᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc){A}(tP : TmP Ω (A [ σ ]T)) → (A ᵃP) (concᵃ' Ω Γc σ)
conPᵃ' Ω Γ σ {El a}   tP = coe (contᵃ' Ω σ a ⁻¹) tP
conPᵃ' Ω Γ σ {Π̂P T B} tP = λ τ → conPᵃ' Ω Γ σ {B τ} (tP $̂P τ)
conPᵃ' Ω Γ σ {a ⇒P A} tP = λ α → conPᵃ' Ω Γ σ {A} (tP $P coe (contᵃ' Ω σ a) α)

conᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc)(σP : SubP σ Ω Γ) → (Γ ᵃC) (concᵃ' Ω Γc σ)
conᵃ' Ω ∙        σ εP        = lift tt
conᵃ' Ω (Γ ▶P A) σ (σP ,P t) = conᵃ' Ω Γ σ σP , conPᵃ' Ω Γ σ {A} t

concᵃ : ∀{Γc}(Γ : Con Γc) → _ᵃc {suc zero} Γc
concᵃ {Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ Γ)
conᵃ Γ = conᵃ' Γ Γ id idP

--some examples
Γnat : Con (∙c ▶c U)
Γnat = ∙ ▶P vz ⇒P El vz ▶P El vz

nat : Set₁
nat = ₂ (concᵃ Γnat)

nzero : nat
nzero = ₂ (conᵃ Γnat)

nsucc : nat → nat
nsucc = ₂ (₁ (conᵃ Γnat))

postulate N : Set
postulate Nz  : N
postulate Ns  : N → N

Γvec : Set → Con (∙c ▶c Π̂S N (λ _ → U))
Γvec A = ∙ ▶P El (vz $S Nz) ▶P (Π̂P A (λ a → Π̂P N λ m → (vz $S m) ⇒P El (vz $S Ns m)))

vec : Set → N → Set₁
vec A = ₂ (concᵃ (Γvec A))

vzero : {A : Set} → vec A Nz
vzero = ₂ (₁ (conᵃ (Γvec _)))

vcons : ∀{A : Set}(a : A) n → vec A n → vec A (Ns n)
vcons = ₂ (conᵃ (Γvec _))
