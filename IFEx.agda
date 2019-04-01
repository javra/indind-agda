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

contᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc)(a : Tm Γc U) → (a ᵃt) (concᵃ' Ω Γc σ) ≡ TmP Ω (El (a [ σ ]t))
contᵃ' Ω Γ ε       a = ⊥-elim (Tm∙c a)
contᵃ' Ω Γ (σ , t) a = {!!}

conPᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc){A}(tP : TmP Ω (A [ σ ]T)) → (A ᵃP) (concᵃ' Ω Γc σ)
conPᵃ' Ω Γ σ {El a}   tP = coe (contᵃ' Ω Γ σ a ⁻¹) tP
conPᵃ' Ω Γ σ {Π̂P T B} tP = λ τ → conPᵃ' Ω Γ σ {B τ} (tP $̂P τ)
conPᵃ' Ω Γ σ {a ⇒P A} tP = λ α → conPᵃ' Ω Γ σ {A} (tP $P coe (contᵃ' Ω Γ σ a) α)

conᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc)(σP : SubP σ Ω Γ) → (Γ ᵃC) (concᵃ' Ω Γc σ)
conᵃ' Ω ∙        σ εP        = lift tt
conᵃ' Ω (Γ ▶P A) σ (σP ,P t) = conᵃ' Ω Γ σ σP , conPᵃ' Ω Γ σ {A} t

concᵃ : ∀{Γc}(Γ : Con Γc) → _ᵃc {suc zero} Γc
concᵃ {Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ Γ)
conᵃ Γ = conᵃ' Γ Γ id idP

--some examples
nat : Set₁
nat = TmP {∙c ▶c U} (∙ ▶P vz ⇒P El vz ▶P El vz) (El vz)

nzero : nat
nzero = vPz

nsucc : nat → nat
nsucc = λ n → vPs vPz $P n

postulate N : Set
postulate Nz  : N
postulate Ns  : N → N

vec : Set → N → Set₁
vec A = λ n → TmP {∙c ▶c Π̂S N (λ _ → U)}
  (∙ ▶P El (vz $S Nz) ▶P (Π̂P A (λ a → Π̂P N λ m → (vz $S m) ⇒P El (vz $S Ns m)))) (El (vz $S n))

vzero : {A : Set} → vec A Nz
vzero = vPs vPz

vcons : ∀{A : Set}(a : A) n → vec A n → vec A (Ns n)
vcons a n v = ((vPz $̂P a) $̂P n) $P v

Γc : SCon
Γc = ∙c ▶c U ▶c U

Γ : Con Γc
Γ = ∙ ▶P El (vs (vz)) ▶P El vz

SΓc : Γc ᵃc
SΓc = concᵃ Γ

SΓ : (Γ ᵃC) SΓc
SΓ = conᵃ Γ

--TmP (∙ ▶P El (var (vvs vvz)) ▶P El (var vvz)) (El (var vvz))
--TmP (∙ ▶P El (var (vvs vvz)) ▶P El (var vvz)) (El (var vvz)) ✓
--TmP (∙ ▶P El (var (vvs vvz)) ▶P El (var vvz)) (El (var (vvs vvz)))
--TmP (∙ ▶P El (var (vvs vvz)) ▶P El (var vvz)) (El (var (vvs vvz))) ✓
