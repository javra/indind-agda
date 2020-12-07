{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFE
open import IFD
open import IFS

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

postulate s : ˢc (ᴱc (∙c ▶c (N ⇒̂S U))) (ʷc Γvec (_ , nᴱ , cᴱ) id)
postulate s' : ˢC (ᴱC Γvec) s {_ , nᴱ , cᴱ} (ʷC Γvec (_ , nᴱ , cᴱ) idP)
postulate a : A

baz = happly (₂ (₁ s')) Nz ⁻¹

baz' : ₂ s (cᴱ a Nz nᴱ) (Ns Nz)
baz' = coe (happly (₂ s' a Nz nᴱ) (Ns Nz) ⁻¹) (_ , coe (happly (₂ (₁ s')) Nz ⁻¹) (_ , refl) , refl)
