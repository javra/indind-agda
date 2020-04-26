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

  ʷP : ∀{A}(tP : TmP Ω A) → ᵈP (ᴱP A) (ʷc id) ((ᴱtP tP ᵃtP) ω)
  ʷP {A} tP = ?

  ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC (ᴱC Γ) (ʷc id) ((ᴱsP σP ᵃsP) ω)
  ʷC εP         = lift tt
  ʷC (σP ,P tP) = ʷC σP , ʷP tP
