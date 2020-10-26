{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF

postulate N A : Set
postulate Nz  : N
postulate Ns  : N → N

open import IFW


Γvec : Con (∙c ▶c N ⇒̂S U)
Γvec = ∙ ▶P El (vz $S Nz) ▶P (Π̂P A (λ a → Π̂P N λ m → (vz $S m) ⇒P El (vz $S Ns m)))

postulate vᴱ : Set
postulate nᴱ : vᴱ
postulate cᴱ : A → N → vᴱ → vᴱ

nʷ = ₂ (₁ (ʷC Γvec (_ , nᴱ , cᴱ) idP))

cʷ = ₂ (ʷC Γvec (_ , nᴱ , cᴱ) idP)
