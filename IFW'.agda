{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFE

module IFW' {Ωc}(Ω : Con Ωc)
  {ωc : _ᵃc {zero} Ωc}(ω : (Ω ᵃC) ωc) where

ʷS : (B : TyS)(β : B ᵃS) → ᵈS {suc zero}{zero} B β
ʷS U        β = λ _ → Set
ʷS (Π̂S T B) β = λ τ → ʷS (B τ) (β τ)

ʷc : ∀{Γc}(σ : Sub Ωc Γc) → ᵈc {suc zero}{zero} Γc ((σ ᵃs) ωc)
ʷc ε                 = lift tt
ʷc (_,_ {B = B} σ t) = ʷc σ , ʷS B ((t ᵃt) ωc)

ʷt : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) → ᵈt t (ʷc σ) ≡ ʷS B ((t ᵃt) ((σ ᵃs) ωc))
ʷt (σ , s) (var vvz)     = refl
ʷt (σ , s) (var (vvs x)) = ʷt σ (var x)
ʷt ε       (t $S τ)      = happly (ʷt ε t) τ
ʷt (σ , s) (t $S τ)      = happly (ʷt (σ , s) t) τ

ʷtid : ∀{B}(t : Tm Ωc B) → ᵈt t (ʷc id) ≡ ʷS B ((t ᵃt) ωc)
ʷtid t = ʷt id t
{-# REWRITE ʷtid #-}

ʷP : ∀ A α (acc : Set) → ᵈP A (ʷc id) α
ʷP (El a)   α acc = acc
ʷP (Π̂P T A) ϕ acc = λ τ → ʷP (A τ) (ϕ τ) acc
ʷP (a ⇒P A) ϕ acc = λ α αᵈ → ʷP A (ϕ α) (acc × αᵈ)

ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC Γ (ʷc id) ((σP ᵃsP) ω)
ʷC εP                   = lift tt
ʷC (_,P_ {A = A} σP tP) = ʷC σP , ʷP A ((tP ᵃtP) ω) ⊤

