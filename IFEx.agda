{-# OPTIONS --rewriting #-}
module IFEx where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS

module Constructor {Ωc}(Ω : Con Ωc) where

  conSᵃ' : ∀{B}(t : Tm Ωc B) → _ᵃS {suc zero} B
  conSᵃ' {U}      t     = TmP Ω (El t)
  conSᵃ' {Π̂S T B} t     = λ τ → conSᵃ' (t $S τ)

  concᵃ' : ∀{Γc}(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
  concᵃ' ε       = lift tt
  concᵃ' (σ , t) = concᵃ' σ , conSᵃ' t

  contᵃ' : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → (t ᵃt) (concᵃ' σ) ≡ conSᵃ' {B} (t [ σ ]t)
  contᵃ' ε       t             = ⊥-elim (Tm∙c t)
  contᵃ' (σ , s) (var vvz)     = refl
  contᵃ' (σ , s) (var (vvs x)) = contᵃ' σ (var x)
  contᵃ' (σ , s) (t $S τ)      = happly (contᵃ' (σ , s) t) τ

  conPᵃ' : ∀{A}(tP : TmP Ω A) → (A ᵃP) (concᵃ' id)
  conPᵃ' {El a}   tP = coe (contᵃ' id a ⁻¹) tP
  conPᵃ' {a ⇒P A} tP = λ α → conPᵃ' {A} (tP $P coe (contᵃ' id a) α)
  conPᵃ' {Π̂P T A} tP = λ τ → conPᵃ' {A τ} (tP $̂P τ)

  conᵃ' : ∀{Γ}(σP : SubP Ω Γ) → (Γ ᵃC) (concᵃ' id)
  conᵃ' εP        = lift tt
  conᵃ' (σP ,P t) = conᵃ' σP , conPᵃ' t

  contPᵃ' : ∀{Γ}(σP : SubP Ω Γ){A}(tP : TmP Γ A) → (tP ᵃtP) (conᵃ' σP) ≡ conPᵃ' {A} (tP [ σP ]tP)
  contPᵃ' εP         tP              = ⊥-elim (TmP∙ tP)
  contPᵃ' (σP ,P sP) (varP vvzP)     = refl
  contPᵃ' (σP ,P sP) (varP (vvsP v)) = contPᵃ' σP (varP v)
  contPᵃ' (σP ,P sP) (tP $P uP)      = contPᵃ' (σP ,P sP) tP ⊗ contPᵃ' (σP ,P sP) uP
                                       ◾ conPᵃ' & (_$P_ (tP [ σP ,P sP ]tP) & coecoe⁻¹ (contᵃ' id _) _)
  contPᵃ' (σP ,P sP) (tP $̂P τ)       = happly (contPᵃ' _ tP) τ

concᵃ : ∀{Ωc}(Ω : Con Ωc) → _ᵃc {suc zero} Ωc
concᵃ {Ωc} Ω = Constructor.concᵃ' Ω id

conᵃ : ∀{Ωc}(Ω : Con Ωc) → (Ω ᵃC) (concᵃ Ω)
conᵃ Ω = Constructor.conᵃ' Ω idP

module Eliminator {Ωc}(Ω : Con Ωc){ωcᵈ}(ωᵈ : ᵈC {suc zero} Ω ωcᵈ (conᵃ Ω)) where

  open Constructor Ω

  elimSᵃ' : ∀{B}(t : Tm Ωc B) → ˢS B (ᵈt t ωcᵈ)
  elimSᵃ' {U}      a = λ α → coe (ᵈt a _ & (contPᵃ' idP (coe (contᵃ' id a) α)
                                 ◾ coecoe⁻¹' (contᵃ' id a) α))
                                   (ᵈtP {suc zero} {suc zero} (coe (contᵃ' id a) α) ωᵈ)
  elimSᵃ' {Π̂S T B} t = λ τ → elimSᵃ' {B τ} (t $S τ)

  elimcᵃ' : ∀{Γc}(σ : Sub Ωc Γc) → ˢc Γc (ᵈs σ ωcᵈ)
  elimcᵃ' ε       = lift tt
  elimcᵃ' (σ , t) = elimcᵃ' σ , elimSᵃ' t

  elimtᵃ' : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → elimSᵃ' (t [ σ ]t) ≡ ˢt t (elimcᵃ' σ)
  elimtᵃ' ε (var ())
  elimtᵃ' (σ , t) (var vvz)     = refl
  elimtᵃ' (σ , t) (var (vvs v)) = elimtᵃ' σ (var v)
  elimtᵃ' σ (t $S τ)            = happly (elimtᵃ' σ t) τ

  elimPᵃ' : ∀{A}(tP : TmP Ω A) → ˢP A (elimcᵃ' id) (ᵈtP tP ωᵈ)
  elimPᵃ' {El a}   tP = coe≡' {q = ᵈt a _ & contPᵃ' idP tP ⁻¹}
                          (apd (ˢt a (elimcᵃ' id)) (contPᵃ' idP tP) ◾ happly (elimtᵃ' id a) (coe (contᵃ' id a ⁻¹) tP) ⁻¹)
                        ◾ coe∘ (ᵈt a ωcᵈ & contPᵃ' idP tP ⁻¹) _
                          (ᵈtP (coe (contᵃ' id a) (coe (contᵃ' id a ⁻¹) tP)) ωᵈ)
                        ◾ ᵈtP≡ tP _ _ (coecoe⁻¹ (contᵃ' id a) tP ⁻¹)
    where ᵈtP≡ : ∀ {A} (tP tP' : TmP Ω A) p (q : tP ≡ tP') → coe p (ᵈtP tP' ωᵈ) ≡ ᵈtP tP ωᵈ
          ᵈtP≡ tP .tP refl refl = refl
  elimPᵃ' {Π̂P T A} tP = λ τ → elimPᵃ' {A τ} (tP $̂P τ)
  elimPᵃ' {a ⇒P A} tP = λ α → let e' = happly (elimtᵃ' id a) α
                                  e = contPᵃ' idP (coe (contᵃ' id a) α) ◾ coecoe⁻¹' (contᵃ' id a) α in
                              coe (ˢPAid≡ (ᵃtP≡ e) (ᵈP A ωcᵈ & ᵃtP≡ e) (ᵈtP≡ _ _ (e ⁻¹) ◾ ᵈtP tP ωᵈ α & e'))
                                   (elimPᵃ' {A} (tP $P coe (contᵃ' id a) α))
    where ˢPAid≡ : ∀ {α α' αᵈ αᵈ'} (p : α ≡ α') p' (q : coe p' αᵈ ≡ αᵈ')
                   → ˢP A (elimcᵃ' id) {α} αᵈ ≡ ˢP A (elimcᵃ' id) {α'} αᵈ'
          ˢPAid≡ refl refl refl = refl
          ᵃtP≡ : ∀ {α α'} (p : α ≡ α') → (tP ᵃtP) (conᵃ Ω) α ≡ (tP ᵃtP) (conᵃ Ω) α'
          ᵃtP≡ refl = refl
          ᵈtP≡ : ∀ {α α' αᵈ} p q (r : α ≡ α') → coe p (ᵈtP tP ωᵈ α' αᵈ) ≡ ᵈtP tP ωᵈ α (coe q αᵈ)
          ᵈtP≡ refl refl refl = refl

  elimᵃ' : ∀{Γ}(σP : SubP Ω Γ) → ˢC Γ (elimcᵃ' id) (ᵈsP σP ωᵈ)
  elimᵃ' εP         = lift tt
  elimᵃ' (σP ,P tP) = elimᵃ' σP , elimPᵃ' tP

elimcᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢc Γc γcᵈ
elimcᵃ Γ γᵈ = Eliminator.elimcᵃ' Γ γᵈ id

elimᵃ : ∀{Γc}(Γ : Con Γc){γcᵈ}(γᵈ : ᵈC Γ γcᵈ (conᵃ Γ)) → ˢC Γ (elimcᵃ Γ γᵈ) γᵈ
elimᵃ Γ γᵈ = Eliminator.elimᵃ' Γ γᵈ idP
{-
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
