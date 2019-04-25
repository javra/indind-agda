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
contᵃ' Ω ε           t                   = ⊥-elim (Tm∙c t)
contᵃ' Ω (σ , s)     (var vvz)           = refl
contᵃ' Ω (σ , s) {B} (var (vvs x))       = contᵃ' Ω σ (var x)
contᵃ' Ω (σ , s) {B} (_$S_ {T}{B''} t α) = happly (contᵃ' Ω (σ , s) {Π̂S T B''} t) α
--{-# REWRITE contᵃ' #

conPᵃ' : ∀{Ωc}(Ω : Con Ωc){A}(tP : TmP Ω A) → (A ᵃP) (concᵃ' Ω Ωc id)
conPᵃ' Ω {El a} tP = coe (contᵃ' Ω id a ⁻¹) tP
conPᵃ' Ω {Π̂P T A} tP = λ τ → conPᵃ' Ω {A τ} (tP $̂P τ)
conPᵃ' Ω {a ⇒P A} tP = λ α → conPᵃ' Ω {A} (tP $P coe (contᵃ' Ω id a) α)

conᵃ' : ∀{Ωc}(Ω Γ : Con Ωc)(σP : SubP id Ω Γ) → (Γ ᵃC) (concᵃ' Ω Ωc id)
conᵃ' Ω ∙        εP        = lift tt
conᵃ' Ω (Γ ▶P A) (σP ,P t) = conᵃ' Ω Γ σP , conPᵃ' Ω {A} t

contPᵃ' : ∀{Ωc}(Ω Γ : Con Ωc)(σP : SubP id Ω Γ){A}(tP : TmP Γ A)
            → (tP ᵃtP) (conᵃ' Ω Γ σP) ≡ conPᵃ' Ω {A} (tP [ σP ]tP)
contPᵃ' Ω ∙        εP         tP              = ⊥-elim (TmP∙ tP)
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (varP vvzP)     = refl
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (varP (vvsP v)) = contPᵃ' Ω Γ σP (varP v)
contPᵃ' Ω (Γ ▶P A) (σP ,P sP)  {A'} (_$P_ {a} tP tP₁)     = contPᵃ' Ω (Γ ▶P A) (σP ,P sP) tP
                                                  ⊗ contPᵃ' Ω (Γ ▶P A) (σP ,P sP) tP₁
                                                ◾ conPᵃ' Ω {A'}
                                                  & coecoe⁻¹' _ _
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (tP $̂P τ)       = happly (contPᵃ' Ω _ _ tP) τ

concᵃ : ∀{Γc}(Γ : Con Γc) → _ᵃc {suc zero} Γc
concᵃ {Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ Γ)
conᵃ Γ = conᵃ' Γ Γ idP
{-
elimSᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω)){B}(t : Tm Ωc B) → ˢS B (ᵈt t ωcᵈ)
elimSᵃ' Ω ωᵈ {U}      t = λ α → coe (ᵈt t _ & contPᵃ' Ω Ω idP {!!})
                                 (lower (ᵈtP {suc zero} (coe (contᵃ' Ω id t) α) ωᵈ))
elimSᵃ' Ω ωᵈ {Π̂S T B} t = λ τ → elimSᵃ' Ω ωᵈ {B τ} (t $S τ)
{-
elimcᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω)){Γc}(σ : Sub Ωc Γc) → ˢc Γc (ᵈs σ ωcᵈ)
elimcᵃ' Ω ωᵈ ε       = lift tt
elimcᵃ' Ω ωᵈ (σ , t) = elimcᵃ' Ω ωᵈ σ , elimSᵃ' Ω ωᵈ t

elimtᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω)){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B)
          → elimSᵃ' Ω ωᵈ (t [ σ ]t) ≡ coe ((ˢS B) & ([]tᵈ t {σ} ⁻¹)) (ˢt t (elimcᵃ' Ω ωᵈ σ))
elimtᵃ' Ω ωᵈ ε (var ())
elimtᵃ' Ω ωᵈ (σ , t) (var vvz)     = refl
elimtᵃ' Ω ωᵈ (σ , t) (var (vvs v)) = elimtᵃ' Ω ωᵈ σ (var v)
elimtᵃ' Ω ωᵈ σ (_$S_ {T} {B} t α) = {!!}

elimPᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω))
           {Γc}(σ : Sub Ωc Γc){A}(tP : TmP Ω (A [ σ ]T))
           → ˢP A (elimcᵃ' Ω ωᵈ σ) (ᵈtP tP ωᵈ)
elimPᵃ' Ω ωᵈ σ {El a}   tP = {!!} --elimtᵃ' Ω ωᵈ σ a
elimPᵃ' Ω ωᵈ σ {Π̂P T A} tP = λ τ → elimPᵃ' Ω ωᵈ σ {A τ} (tP $̂P τ)
elimPᵃ' Ω ωᵈ σ {a ⇒P A} tP = λ α → {!!}

elimᵃ' :  ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω))
           {Γc}(Γ : Con Γc){σ}(σP : SubP σ Ω Γ) → ˢC Γ (elimcᵃ' Ω ωᵈ σ) (ᵈsP σP ωᵈ)
elimᵃ' Ω ωᵈ ∙        εP         = lift tt
elimᵃ' Ω ωᵈ (Γ ▶P A) (σP ,P tP) = elimᵃ' Ω ωᵈ Γ σP , elimPᵃ' Ω ωᵈ _ tP

elimcᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢc Γc γcᵈ
elimcᵃ Γ γᵈ = elimcᵃ' Γ γᵈ id

elimᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢC Γ (elimcᵃ Γ γᵈ) γᵈ
elimᵃ Γ γᵈ = elimᵃ' Γ γᵈ Γ idP

--some examples
Γnat : Con (∙c ▶c U)
Γnat = ∙ ▶P vz ⇒P El vz ▶P El vz

nat : Set₁
nat = ₂ (concᵃ Γnat)

nzero : nat
nzero = ₂ (conᵃ Γnat)

nsucc : nat → nat
nsucc = ₂ (₁ (conᵃ Γnat))

nrec : ∀(P : nat → Set₁)(ps : ∀ n → P n → P (nsucc n))(pz : P nzero) → ∀ n → P n
nrec P ps pz = elimSᵃ' Γnat (_ , (λ m p → lift (ps m p)) , lift pz) vz

Γuu : Con (∙c ▶c U ▶c U)
Γuu = ∙ ▶P El (vs vz) ▶P El vz

uu1 : Set₁
uu1 = ₂ (₁ (concᵃ Γuu))

uu2 : Set₁
uu2 = ₂ (concᵃ Γuu)

st1 : uu1
st1 = ₂ (₁ (conᵃ Γuu))

st2 : uu2
st2 = ₂ (conᵃ Γuu)

uurec : ∀(P : uu1 → Set₁)(Q : uu2 → Set₁)(p : P st1)(q : Q st2) →
         ˢc (∙c ▶c U ▶c U) (_ , P , Q)
uurec P Q p q = elimcᵃ Γuu (_ , lift p , lift q)

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
-}
