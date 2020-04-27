{-# OPTIONS --rewriting #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFE

module IFW {Ωc}(Ω : Con Ωc)
  {ωc : _ᵃc {zero} (ᴱc Ωc)}(ω : (ᴱC Ω ᵃC) ωc) where

  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  ʷS : (B : TyS) → Set₁
  ʷS U        = Set
  ʷS (Π̂S T B) = (τ : T) → ʷS (B τ)

  ʷc : ∀{Γc}(σ : Sub Ωc Γc) → ᵈc {suc zero} (ᴱc Γc) ((ᴱs σ ᵃs) ωc)
  ʷc ε                 = lift tt
  ʷc (_,_ {B = B} σ t) = ʷc σ , λ _ → ʷS B

  rhs : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → Set₁
  rhs σ (var {B} x)       = ʷS B
  rhs σ (_$S_ {T}{B} t τ) = rhs σ t

  ʷt : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) α
       → ᵈt (ᴱt t) (ʷc σ) α ≡ rhs σ t
  ʷt (σ , s) (var vvz)     α = refl
  ʷt (σ , s) (var (vvs x)) α = ʷt σ (var x) α
  ʷt ε       (t $S τ)      α = ʷt ε t α
  ʷt (σ , s) (t $S τ)      α = ʷt (σ , s) t α

  ʷtid : ∀{B}(t : Tm Ωc B) α → ᵈt (ᴱt t) (ʷc id) α ≡ rhs id t
  ʷtid t α = ʷt id t α
  {-# REWRITE ʷtid #-}

  ʷP : ∀{A}(tP : TmP Ω A) → ᵈP (ᴱP A) (ʷc id) ((ᴱtP tP ᵃtP) ω)
  ʷP {El a} tP = {!!}
  ʷP {Π̂P T A} tP = {!!} --maybe defer, needs ext ctxt
  ʷP {a ⇒P A} tP = λ α αᵈ → {!!}

  ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC (ᴱC Γ) (ʷc id) ((ᴱsP σP ᵃsP) ω)
  ʷC εP         = lift tt
  ʷC (σP ,P tP) = ʷC σP , ʷP tP
