{-# OPTIONS --rewriting #-}
module IFEx_REW where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS

conSᵃ' : ∀{Ωc}(Ω : Con Ωc){B}(t : Tm Ωc B) → _ᵃS {suc zero} B
conSᵃ' Ω {U}      t     = TmP Ω (El t)
conSᵃ' Ω {T ⇒̂S B} t     = λ τ → conSᵃ' Ω (t $S τ)

concᵃ' : ∀{Ωc}(Ω : Con Ωc)(Γc : SCon)(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
concᵃ' Ω ∙c        ε       = lift tt
concᵃ' Ω (Γc ▶c B) (σ , t) = concᵃ' Ω Γc σ , conSᵃ' Ω t

contᵃ' : ∀{Ωc}(Ω : Con Ωc){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B)
           → (t ᵃt) (concᵃ' Ω Γc σ) ≡ conSᵃ' Ω {B} (t [ σ ]t)
contᵃ' Ω ε           t                   = ⊥-elim (Tm∙c t)
contᵃ' Ω (σ , s)     (var vvz)           = refl
contᵃ' Ω (σ , s) {B} (var (vvs x))       = contᵃ' Ω σ (var x)
contᵃ' Ω (σ , s) {B} (_$S_ {T}{B''} t α) = happly (contᵃ' Ω (σ , s) {T ⇒̂S B''} t) α
{-# REWRITE contᵃ' #-}

contᵃ'' : ∀{Ωc}(Ω : Con Ωc){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B)
           → conSᵃ' Ω {B} (t [ σ ]t) ≡ conSᵃ' Ω {B} (t [ σ ]t [ id ]t)
contᵃ'' Ω σ t = refl
--{-# REWRITE contᵃ'' #-}

conPᵃ' : ∀{Ωc}(Ω : Con Ωc){A}(tP : TmP Ω A) → (A ᵃP) (concᵃ' Ω Ωc id)
conPᵃ' Ω {El a} tP = tP
conPᵃ' Ω {Π̂P T A} tP = λ τ → conPᵃ' Ω {A τ} (tP $̂P τ)
conPᵃ' Ω {a ⇒P A} tP = λ α → conPᵃ' Ω {A} (tP $P α)

conᵃ' : ∀{Ωc}(Ω Γ : Con Ωc)(σP : SubP Ω Γ) → (Γ ᵃC) (concᵃ' Ω Ωc id)
conᵃ' Ω ∙        εP         = lift tt
conᵃ' Ω (Γ ▶P A) (σP ,P tP) = conᵃ' Ω Γ σP , conPᵃ' Ω {A} tP

contPᵃ' : ∀{Ωc}(Ω Γ : Con Ωc)(σP : SubP Ω Γ){A}(tP : TmP Γ A)
            → (tP ᵃtP) (conᵃ' Ω Γ σP) ≡ conPᵃ' Ω {A} (tP [ σP ]tP)
contPᵃ' Ω ∙        εP         tP              = ⊥-elim (TmP∙ tP)
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (varP vvzP)     = refl
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (varP (vvsP v)) = contPᵃ' Ω Γ σP (varP v)
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (tP $P uP)      = contPᵃ' Ω (Γ ▶P A) (σP ,P sP) tP
                                                  ⊗ contPᵃ' Ω (Γ ▶P A) (σP ,P sP) uP
contPᵃ' Ω (Γ ▶P A) (σP ,P sP) (tP $̂P τ)       = happly (contPᵃ' Ω _ _ tP) τ
{-# REWRITE contPᵃ' #-}

concᵃ : ∀{Γc}(Γ : Con Γc) → _ᵃc {suc zero} Γc
concᵃ {Γc} Γ = concᵃ' Γ Γc id

conᵃ : ∀{Γc}(Γ : Con Γc) → (Γ ᵃC) (concᵃ Γ)
conᵃ Γ = conᵃ' Γ Γ idP

elimSᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC {suc zero} Ω ωcᵈ (conᵃ Ω)){B}(t : Tm Ωc B) → ˢS B (ᵈt t ωcᵈ)
elimSᵃ' Ω ωᵈ {U}      t = λ α → ᵈtP α ωᵈ
elimSᵃ' Ω ωᵈ {T ⇒̂S B} t = λ τ → elimSᵃ' Ω ωᵈ {B} (t $S τ)

elimcᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω)){Γc}(σ : Sub Ωc Γc) → ˢc Γc (ᵈs σ ωcᵈ)
elimcᵃ' Ω ωᵈ ε       = lift tt
elimcᵃ' Ω ωᵈ (σ , t) = elimcᵃ' Ω ωᵈ σ , elimSᵃ' Ω ωᵈ t

elimtᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC {suc zero} Ω ωcᵈ (conᵃ Ω)){Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B)
          →  (elimSᵃ' Ω ωᵈ (t [ σ ]t)) ≡  coe {!!} (ˢt t (elimcᵃ' Ω ωᵈ σ))
elimtᵃ' Ω ωᵈ ε (var ())
elimtᵃ' Ω ωᵈ (σ , t) (var vvz)     = refl
elimtᵃ' Ω ωᵈ (σ , t) (var (vvs v)) = elimtᵃ' Ω ωᵈ σ (var v)
elimtᵃ' Ω ωᵈ σ (_$S_ {T} {B} t τ)  = {!!}

elimPᵃ' : ∀{Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω)){A}(tP : TmP Ω A)
           → ˢP A (elimcᵃ' Ω ωᵈ id) (ᵈtP tP ωᵈ)
elimPᵃ' Ω ωᵈ {El a}   tP = {!!} --elimtᵃ' Ω ωᵈ σ a
elimPᵃ' Ω ωᵈ {Π̂P T A} tP = λ τ → elimPᵃ' Ω ωᵈ {A τ} (tP $̂P τ)
elimPᵃ' Ω ωᵈ {a ⇒P A} tP = λ α → coe (ˢP A (elimcᵃ' Ω ωᵈ id)
                                   & (ᵈtP tP ωᵈ α & {!!}))
                                 (elimPᵃ' Ω ωᵈ (tP $P α))

elimᵃ' :  ∀{Ωc}(Ω Γ : Con Ωc){ωcᵈ}(ωᵈ : ᵈC Ω ωcᵈ (conᵃ Ω))
           (σP : SubP Ω Γ) → ˢC Γ (elimcᵃ' Ω ωᵈ id) (ᵈsP σP ωᵈ)
elimᵃ' Ω ∙ ωᵈ σP = lift tt
elimᵃ' Ω (Γ ▶P A) ωᵈ (σP ,P tP) = elimᵃ' Ω Γ ωᵈ σP , elimPᵃ' Ω ωᵈ {A} tP

elimcᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢc Γc γcᵈ
elimcᵃ Γ γᵈ = elimcᵃ' Γ γᵈ id

elimᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢC Γ (elimcᵃ Γ γᵈ) γᵈ
elimᵃ Γ γᵈ = elimᵃ' Γ Γ γᵈ idP

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
nrec P ps pz = elimSᵃ' Γnat (_ , (λ m p → ps m p) , pz) vz

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
uurec P Q p q = elimcᵃ Γuu (_ , p , q)

postulate N : Set
postulate Nz  : N
postulate Ns  : N → N

Γvec : Set → Con (∙c ▶c N ⇒̂S U)
Γvec A = ∙ ▶P El (vz $S Nz) ▶P (Π̂P A (λ a → Π̂P N λ m → (vz $S m) ⇒P El (vz $S Ns m)))

vec : Set → N → Set₁
vec A = ₂ (concᵃ (Γvec A))

vzero : {A : Set} → vec A Nz
vzero = ₂ (₁ (conᵃ (Γvec _)))

vcons : ∀{A : Set}(a : A) n → vec A n → vec A (Ns n)
vcons = ₂ (conᵃ (Γvec _))
