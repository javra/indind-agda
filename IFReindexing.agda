{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFS
open import IFEx
open import IFW
open import IFE

open Constructor

-- Assume sections of the wellformedness predicate as given
-- by the assumed existence of inductive families
module IFReindexing {Ωc}(Ω : Con Ωc)
  (ʷˢc : ˢc (ᴱc Ωc) (ʷc Ω (conᵃ (ᴱC Ω)) id))
  (ʷˢC : ˢC (ᴱC Ω) ʷˢc (ʷC Ω (conᵃ (ᴱC Ω)) idP)) where

ᴿS'' : ∀{B}(t : Tm Ωc B) → _ᵃS {suc zero} B
ᴿS'' {U}      t = ∃ λ α → hdfill Ω (conᵃ (ᴱC Ω)) t (ˢt (ᴱt t) ʷˢc α)
ᴿS'' {T ⇒̂S B} t = λ τ → ᴿS'' (t $S τ)

ᴿc : ∀{Γc}(σ : Sub Ωc Γc) → _ᵃc {suc zero} Γc
ᴿc ε       = lift tt
ᴿc (σ , t) = ᴿc σ , ᴿS'' t
