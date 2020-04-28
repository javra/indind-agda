{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFE

module IFW {Ωc}(Ω : Con Ωc)
  {ωc : _ᵃc {zero} (ᴱc Ωc)}(ω : (ᴱC Ω ᵃC) ωc) where

ʷS : TyS → Set₁
ʷS U        = Set
ʷS (Π̂S T B) = (τ : T) → ʷS (B τ)

ʷc : ∀{Γc}(σ : Sub Ωc Γc) → ᵈc {suc zero} (ᴱc Γc) ((ᴱs σ ᵃs) ωc)
ʷc ε                 = lift tt
ʷc (_,_ {B = B} σ t) = ʷc σ , λ _ → ʷS B

ʷS' : ∀{Γc B}(t : Tm Γc B) → Set₁
ʷS' (var {B} x)       = ʷS B
ʷS' (_$S_ {T}{B} t τ) = ʷS' t

ʷt : ∀{Γc}(σ : Sub Ωc Γc){B}(t : Tm Γc B) α → ᵈt (ᴱt t) (ʷc σ) α ≡ ʷS' t
ʷt (σ , s) (var vvz)     α = refl
ʷt (σ , s) (var (vvs x)) α = ʷt σ (var x) α
ʷt ε       (t $S τ)      α = ʷt ε t α
ʷt (σ , s) (t $S τ)      α = ʷt (σ , s) t α

ʷtid : ∀{B}(t : Tm Ωc B) α → ᵈt (ᴱt t) (ʷc id) α ≡ ʷS B --ʷS' id t
ʷtid t α = {!!} --ʷt id t α --this is temporary to ignore Π̂S
{-# REWRITE ʷtid #-}


ʷP : ∀ A (α : (ᴱP A ᵃP) ωc)(acc : Set) → ᵈP (ᴱP A) (ʷc id) α
ʷP (El a) α acc = acc
ʷP (Π̂P T A) ϕ acc = λ τ → ʷP (A τ) (ϕ τ) acc
ʷP (a ⇒P A) ϕ acc = λ α αᵈ → ʷP A (ϕ α) (acc × αᵈ)

ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC (ᴱC Γ) (ʷc id) ((ᴱsP σP ᵃsP) ω)
ʷC εP                   = lift tt
ʷC (_,P_ {A = A} σP tP) = ʷC σP , ʷP A ((ᴱtP tP ᵃtP) ω) ⊤
