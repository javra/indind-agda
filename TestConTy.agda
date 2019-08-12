{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import II using (PS; P; S)
open import EWRSg
open import Lib

module TestConTy where

Γ : Con
Γ = ∙ ▶S U -- Con
      ▶S ΠS (vz{S}) U -- Ty

Γ' : Con
Γ' = Γ ▶P El (vs{S}{S} (vz{S})) -- nil

Γ''aux : Con
Γ''aux = Γ' ▶P El (vs{S}{P}{Γ} (vs{S}{S} (vz{S})))

Γ'' : Con
Γ'' = Γ' ▶P ΠP {Γ'} (vs{S}{P}{Γ} (vs{S}{S}{∙ ▶S U} (vz{S})))
                    (ΠP{Γ''aux} (appS{Γ'} (vs{S}{P}{Γ} (vz{S})))
                                (El (vs{S}{P}{Γ''aux} (vs{S}{P}{Γ'} (vs{S}{P}{Γ} (vs{S}{S}{∙ ▶S U} vz)))))) --ext

