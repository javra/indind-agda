{-# OPTIONS --rewriting #-}
module IFEx where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS

data VarP {ℓ Γc} : Con Γc → TyP Γc → Set (suc ℓ) where
  vvPz : ∀{Γ A} → VarP (Γ ▶P A) A
  vvPs : ∀{Γ A B} → VarP {ℓ} Γ A → VarP (Γ ▶P B) A

data TmP {ℓ Γc}(Γ : Con Γc) : TyP Γc → Set (suc ℓ) where
  varP : ∀{A} → VarP {ℓ} Γ A → TmP Γ A
  _$P_ : ∀{a A} → TmP {ℓ} Γ (a ⇒P A) → TmP {ℓ} Γ (El a) → TmP Γ A
  _$̂P_ : ∀{T A} → TmP {ℓ} Γ (Π̂P T A) → (τ : T) → TmP Γ (A τ)

data SubP {ℓ Γc Δc}(σ : Sub Γc Δc) : ∀(Γ : Con Γc)(Δ : Con Δc) → Set (suc ℓ) where
  εP   : ∀{Γ} → SubP σ Γ ∙
  _,P_ : ∀{Γ Δ A} → SubP {ℓ} σ Γ Δ → TmP {ℓ} Γ (A [ σ ]T) → SubP σ Γ (Δ ▶P A)

vPz : ∀{ℓ Γc Γ A} → TmP {ℓ}{Γc} (Γ ▶P A) A
vPz = varP vvPz

vPs : ∀{ℓ Γc Γ A B} → TmP {ℓ}{Γc} Γ A → TmP (Γ ▶P B) A
vPs (varP x) = varP (vvPs x)
vPs (f $P t) = vPs f $P vPs t
vPs (f $̂P τ) = vPs f $̂P τ

wkP : ∀{ℓ Γc Δc}{σ : Sub Γc Δc}{Γ Δ A} → SubP {ℓ} σ Γ Δ → SubP {ℓ} σ (Γ ▶P A) Δ
wkP εP        = εP
wkP (σP ,P t) = wkP σP ,P vPs t

idP : ∀{ℓ Γc}{Γ : Con Γc} → SubP {ℓ} id Γ Γ
idP {Γ = ∙}      = εP
idP {Γ = Γ ▶P B} = wkP idP ,P vPz

conSᵃ' : ∀{ℓ Ωc}(Ω : Con Ωc){B}(t : Tm Ωc B) → _ᵃS {suc ℓ} B
conSᵃ' Ω {U}      t     = TmP Ω (El t)
conSᵃ' Ω {Π̂S T B} t     = λ τ → conSᵃ' Ω (t $S τ)

concᵃ' : ∀{ℓ Ωc}(Ω : Con Ωc)(Γc : SCon)(σ : Sub Ωc Γc) → _ᵃc {suc ℓ} Γc
concᵃ' Ω ∙c        ε       = lift tt
concᵃ' Ω (Γc ▶c B) (σ , t) = concᵃ' Ω Γc σ , conSᵃ' Ω t

contᵃ' : ∀{ℓ Ωc}(Ω : Con Ωc){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → (t ᵃt) (concᵃ' Ω Γc σ) ≡ conSᵃ'{ℓ} Ω {B} (t [ σ ]t)
contᵃ' Ω            ε           t                   = ⊥-elim (Tm∙c t)
contᵃ' Ω            (σ , s)     (var vvz)           = refl
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (var (vvs x))       = contᵃ' Ω σ (var x)
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (_$S_ {T}{B''} t α) = happly (contᵃ' Ω (σ , s) {Π̂S T B''} t) α

conPᵃ' : ∀{ℓ Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc){A}(tP : TmP Ω (A [ σ ]T)) → (A ᵃP) (concᵃ' {ℓ} Ω Γc σ)
conPᵃ' Ω Γ σ {El a}   tP = coe (contᵃ' Ω σ a ⁻¹) tP
conPᵃ' Ω Γ σ {Π̂P T B} tP = λ τ → conPᵃ' Ω Γ σ {B τ} (tP $̂P τ)
conPᵃ' Ω Γ σ {a ⇒P A} tP = λ α → conPᵃ' Ω Γ σ {A} (tP $P coe (contᵃ' Ω σ a) α)

conᵃ' : ∀{ℓ Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc)(σP : SubP {ℓ} σ Ω Γ) → (Γ ᵃC) (concᵃ' {ℓ} Ω Γc σ)
conᵃ' Ω ∙        σ εP        = lift tt
conᵃ' Ω (Γ ▶P A) σ (σP ,P t) = conᵃ' Ω Γ σ σP , conPᵃ' Ω Γ σ {A} t

concᵃ : ∀{ℓ Γc}(Γ : Con Γc) → _ᵃc {suc ℓ} Γc
concᵃ {ℓ}{Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{ℓ Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ {ℓ} Γ)
conᵃ Γ = conᵃ' Γ Γ id idP

elimSᵃ' : ∀{ℓ ℓ' Ωc}(Ω : Con Ωc){B}{t : Tm Ωc B}(αᵈ : ᵈS {ℓ'} B (conSᵃ' {ℓ} Ω t)) → ˢS B αᵈ
elimSᵃ' Ω {U}      {t} αᵈ x = {!!}
elimSᵃ' Ω {Π̂S T B} {t} αᵈ τ = elimSᵃ' Ω {B τ} {t $S τ} (αᵈ τ)

elimcᵃ' : ∀{ℓ ℓ' Ωc}(Ω : Con Ωc){Γc : SCon}(Γ : Con Γc){σ}(σP : SubP σ Ω Γ){γcᵈ}
  (γᵈ : ᵈC {ℓ'} Γ γcᵈ (conᵃ' {ℓ} Ω Γ σ σP)) → ˢc Γc γcᵈ
elimcᵃ' Ω {∙c} Γ {ε} σP γᵈ = lift tt
elimcᵃ' Ω {Γc ▶c B} Γ {σ , t} σP {γcᵈ , αᵈ} γᵈ = elimcᵃ' Ω {!!} {!!} {!!} , {!!}

elimᵃ' : ∀{ℓ ℓ' Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc){σ}(σP : SubP σ Ω Γ)
  {γcᵈ}(γᵈ : ᵈC {ℓ'} Γ γcᵈ (conᵃ' {ℓ} Ω Γ σ σP))
  → ˢC Γ (elimcᵃ' Ω Γ σP γᵈ) γᵈ
elimᵃ' = {!!}

elimcᵃ : ∀{ℓ ℓ' Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC {ℓ'} Γ γcᵈ (conᵃ {ℓ} Γ)) → ˢc Γc γcᵈ
elimcᵃ Γ γᵈ = elimcᵃ' Γ Γ idP γᵈ

elimᵃ : ∀{ℓ ℓ'}{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC {ℓ'} Γ γcᵈ (conᵃ {ℓ} Γ)) → ˢC Γ (elimcᵃ Γ γᵈ) γᵈ
elimᵃ Γ γᵈ = elimᵃ' Γ Γ idP γᵈ

--some examples
Γnat : Con (∙c ▶c U)
Γnat = ∙ ▶P vz ⇒P El vz ▶P El vz

nat : Set₁
nat = ₂ (concᵃ Γnat)

nzero : nat
nzero = ₂ (conᵃ Γnat)

nsucc : nat → nat
nsucc = ₂ (₁ (conᵃ Γnat))

nrec : ∀(P : nat → Set₁)(pz : P nzero)(ps : ∀ n → P n → P (nsucc n)) → ∀ n → P n
nrec P pz ps n = {!!}

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
