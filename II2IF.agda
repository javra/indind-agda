{-# OPTIONS --rewriting --allow-unsolved-metas #-}
import IF as s
open import EWRSg
open import IFA
open import IFD
open import IFS

module II2IF
  (concᵃ  : ∀{ℓ}(Δc : s.SCon) → _ᵃc {ℓ} Δc)
  (conᵃ   : ∀{ℓ}{Δc}(Δ : s.Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δc))
  (elimcᵃ : ∀{ℓ ℓ'}(Δc : s.SCon)(δcᵈ : ᵈc {ℓ'} Δc (concᵃ {ℓ} Δc)) → ˢc Δc δcᵈ)
  (elimᵃ  : ∀{ℓ ℓ'}{Δc}(Δ : s.Con Δc){δcᵈ}(δᵈ : ᵈC {ℓ'} Δ δcᵈ (conᵃ {ℓ} Δ)) → ˢC Δ (elimcᵃ Δc δcᵈ) δᵈ) where

con : (Γ : Con) → Con.ᴬ Γ
con Γ = let Ecᵃ = concᵃ Γ.Ec in
        let Eᵃ  = conᵃ Γ.E in
        let wcᵃ = concᵃ (Γ.wc Eᵃ) in
        let wᵃ  = conᵃ (Γ.w Eᵃ) in
        Γ.sg Ecᵃ Eᵃ wcᵃ wᵃ
  where module Γ = Con Γ
