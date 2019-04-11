{-# OPTIONS --rewriting #-}
module IFEx where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS

conSᵃ' : ∀{Ωc}(Ω : Con Ωc){B}(t : Tm Ωc B) → _ᵃS {suc zero} B
conSᵃ' Ω {U}      t     = TmP Ω (El t)
conSᵃ' Ω {Π̂S T B} t     = λ τ → conSᵃ' Ω (t $S τ)

concᵃ' : ∀{Ωc}(Ω : Con Ωc)(Γc : SCon)(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
concᵃ' Ω ∙c        ε       = lift tt
concᵃ' Ω (Γc ▶c B) (σ , t) = concᵃ' Ω Γc σ , conSᵃ' Ω t

contᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B)
           → (t ᵃt) (concᵃ' Ω Γc σ) ≡ conSᵃ' Ω {B} (t [ σ ]t)
contᵃ' Ω            ε           t                   = ⊥-elim (Tm∙c t)
contᵃ' Ω            (σ , s)     (var vvz)           = refl
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (var (vvs x))       = contᵃ' Ω σ (var x)
contᵃ' Ω {Γc ▶c B'} (σ , s) {B} (_$S_ {T}{B''} t α) = happly (contᵃ' Ω (σ , s) {Π̂S T B''} t) α

conPᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc){A}(tP : TmP Ω (A [ σ ]T))
           → (A ᵃP) (concᵃ' Ω Γc σ)
conPᵃ' Ω Γ σ {El a}   tP = coe (contᵃ' Ω σ a ⁻¹) tP
conPᵃ' Ω Γ σ {Π̂P T B} tP = λ τ → conPᵃ' Ω Γ σ {B τ} (tP $̂P τ)
conPᵃ' Ω Γ σ {a ⇒P A} tP = λ α → conPᵃ' Ω Γ σ {A} (tP $P coe (contᵃ' Ω σ a) α)

conᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc)(σ : Sub Ωc Γc)(σP : SubP σ Ω Γ)
          → (Γ ᵃC) (concᵃ' Ω Γc σ)
conᵃ' Ω ∙        σ εP        = lift tt
conᵃ' Ω (Γ ▶P A) σ (σP ,P t) = conᵃ' Ω Γ σ σP , conPᵃ' Ω Γ σ {A} t

concᵃ : ∀{Γc}(Γ : Con Γc) → _ᵃc {suc zero} Γc
concᵃ {Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ Γ)
conᵃ Γ = conᵃ' Γ Γ id idP

elimSᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω))
            {Γc}{Γ : Con Γc}{σ}(σP : SubP σ Ω Γ){B}(t : Tm Ωc B)
            → ˢS B (ᵈt t ωcᵈ)
elimSᵃ' Ω ωᵈ {σ = σ} σP {U}      t = λ α → {!!} -- (coe (contᵃ' Ω id t) α)
elimSᵃ' Ω ωᵈ         σP {Π̂S T B} t = λ τ → elimSᵃ' Ω ωᵈ σP {B τ} (t $S τ)

elimcᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω))
           {Γc : SCon}(Γ : Con Γc){σ}(σP : SubP σ Ω Γ)
             → ˢc Γc (ᵈs σ ωcᵈ)
elimcᵃ' Ω ωᵈ {∙c} Γ σP = lift tt
elimcᵃ' Ω ωᵈ {Γc ▶c B} Γ σP = elimcᵃ' Ω ωᵈ {Γc} {!!} {!!} , {!!} --elimSᵃ' Ω {!!} {!!}
{-
elimᵃ' : ∀{ℓ ℓ' Ωc}(Ω : Con Ωc){Γc}(Γ : Con Γc){σ}(σP : SubP σ Ω Γ)
  {γcᵈ}(γᵈ : ᵈC {ℓ'} Γ γcᵈ (conᵃ' {ℓ} Ω Γ σ σP))
  → ˢC Γ (elimcᵃ' Ω Γ σP γᵈ) γᵈ
elimᵃ' Ω ∙ εP γᵈ = lift tt
elimᵃ' Ω (Γ ▶P A) (σP ,P tP) (γᵈ , αᵈ) = {!!} , {!!}

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
-}
