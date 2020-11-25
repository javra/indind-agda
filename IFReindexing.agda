{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS
open import IFEx
import IFW
open import IFE

open Constructor

-- Assume sections of the wellformedness predicate as given
-- by the assumed existence of inductive families
module IFReindexing {Ωc}(Ω : Con Ωc)
  {ωc : _ᵃc {suc zero} (ᴱc Ωc)}
  (ω : _ᵃC {suc zero} (ᴱC Ω) ωc)
  (ωcˢ  : ˢc (ᴱc Ωc) (IFW.ʷc Ω ω id))
  (ωˢ : ˢC (ᴱC Ω) ωcˢ (IFW.ʷC Ω ω idP)) where

open IFW Ω ω

ᴿS : ∀{B}(t : Tm Ωc B) → _ᵃS {suc zero} B
ᴿS {U}      t = ∃ λ α → hdfill t (ˢt (ᴱt t) ωcˢ α)
ᴿS {T ⇒̂S B} t = λ τ → ᴿS (t $S τ)

ᴿc : ∀{Γc}(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
ᴿc ε       = lift tt
ᴿc (σ , t) = ᴿc σ , ᴿS t

ᴿt= : ∀{B}{Γc}(σ : Sub Ωc Γc)(t : Tm Γc B) → (t ᵃt) (ᴿc σ) ≡ ᴿS (t [ σ ]t)
ᴿt= (σ , s) (var vvz)     = refl
ᴿt= (σ , s) (var (vvs v)) = ᴿt= σ (var v)
ᴿt=  ε      (t $S τ)      = happly (ᴿt= ε t) τ
ᴿt= (σ , s) (t $S τ)      = happly (ᴿt= (σ , s) t) τ

ᴿt=id : ∀{B}(t : Tm Ωc B) → (t ᵃt) (ᴿc id) ≡ ᴿS t
ᴿt=id t = ᴿt= id t
{-# REWRITE ᴿt=id #-}

ᴿv : ∀(v : Var Ωc U) α → ˢt (ᴱt (var v)) ωcˢ α
ᴿv vvz α = {!!}
ᴿv (vvs v) α = {!!}

ᴿt : ∀{B}(t : Tm Ωc U) α → hdfill t (ˢt (ᴱt t) ωcˢ α)
ᴿt t α = {!!}

ᴿP : ∀ A (α : (ᴱP A ᵃP) ωc) (αˢ : ˢP (ᴱP A) ωcˢ (ʷP A α (Lift _ ⊤))) → _ᵃP {suc zero} A (ᴿc id)
ᴿP (El a)   α αˢ = α , {!!} --coe (hdfill a & (αˢ ⁻¹)) {!!}
ᴿP (Π̂P T A) ϕ ϕˢ = λ τ → ᴿP (A τ) (ϕ τ) (ϕˢ τ)
ᴿP (a ⇒P A) ϕ ϕˢ = λ α → ᴿP A (ϕ (₁ α)) {!!}

ᴿP' : ∀{A}(tP : TmP Ω A) → _ᵃP {suc zero} A (ᴿc id)
ᴿP' {El a}   tP = (ᴱtP tP ᵃtP) ω , {!!}
ᴿP' {Π̂P T A} tP = λ τ → ᴿP' (tP $̂P τ)
ᴿP' {a ⇒P A} tP = λ { α → ᴿP' {A} (tP $P {!!}) } -- nope

ᴿC : ∀{Γ}(σP : SubP Ω Γ) → _ᵃC {suc zero} Γ (ᴿc id)
ᴿC εP                   = lift tt
ᴿC (_,P_ {A = A} σP tP) = ᴿC σP , ᴿP A ((ᴱtP tP ᵃtP) ω) {!!} --(ˢtP (ᴱtP tP) ωˢ)
