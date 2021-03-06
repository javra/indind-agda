{-# OPTIONS --rewriting --allow-unsolved-metas #-}
import IF as s
open import EWRSg
open import IFA
open import IFD
open import IFS
open import IFEx using (concᵃ; conᵃ)

module II2IF
  (elimcᵃ : ∀{ℓ ℓ'}{Δc}(Δ : s.Con Δc){δcᵈ}(δᵈ : ᵈC {ℓ'} Δ δcᵈ (conᵃ {ℓ} Δ)) → ˢc Δc δcᵈ)
  (elimᵃ  : ∀{ℓ ℓ'}{Δc}(Δ : s.Con Δc){δcᵈ}(δᵈ : ᵈC {ℓ'} Δ δcᵈ (conᵃ {ℓ} Δ)) → ˢC Δ (elimcᵃ Δ δᵈ) δᵈ) where

con : (Γ : Con) → Con.ᴬ Γ
con Γ = let Ecᵃ = concᵃ Γ.E in
        let Eᵃ  = conᵃ Γ.E in
        let wcᵃ = concᵃ (Γ.w Eᵃ) in
        let wᵃ  = conᵃ (Γ.w Eᵃ) in
        Γ.sg Ecᵃ Eᵃ wcᵃ wᵃ
  where module Γ = Con Γ
