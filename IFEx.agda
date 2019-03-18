{-# OPTIONS --rewriting #-}
module IFEx where

open import Lib hiding (id; _∘_)
open import IF
open import IFA

data ic : SCon → Set
data iS : TyS → Set

data ic where
  ivz : ∀{Γc B} → iS B  → ic (Γc ▶c B)
  ivs : ∀{Γc B} → ic Γc → ic (Γc ▶c B)

data iS where
  iU  : iS U
  iΠ̂S : ∀{T B} → (τ : T) → iS (B τ) → iS (Π̂S T B)

ft : ∀{Γc}{B}(a : Tm Γc B)(i : iS B) → ic Γc
ft (var vvz)     i = ivz i
ft (var (vvs t)) i = ivs (ft (var t) i)
ft (t $S α)      i = ft t (iΠ̂S α i)

data fC {ℓ : Level} : ∀{Γc : SCon}(Γ : Con Γc) → ic Γc → Set (suc ℓ)
data iP {ℓ : Level} : ∀{Γc : SCon}(Γ : Con Γc)(A : TyP Γc) → Set (suc ℓ)

iSP : ∀{ℓ : Level}{Γc : SCon}{Γ : Con Γc}{A : TyP Γc} → iP {ℓ} Γ A → ic Γc

data fC {ℓ : Level} where
  fSs : ∀{Γc}{Γ : Con Γc}{B i} → fC {ℓ} Γ i → fC (Γ ▶S B) (ivs i)
  fPs : ∀{Γc}{Γ : Con Γc}{A i} → fC {ℓ} Γ i → fC (Γ ▶P A) i
  fPz : ∀{Γc}{Γ : Con Γc}{A}(ι : iP {ℓ} (Γ ▶P A) A) → fC (Γ ▶P A) (iSP ι) --???
  
data iP {ℓ : Level} where
  iEl : ∀{Γc Γ}{a : Tm Γc U} → iP Γ (El a)
  iΠ̂P : ∀{Γc Γ T}{B : T → TyP Γc}(x : T) → iP {ℓ} Γ (B x) → iP Γ (Π̂P T B)
  i⇒P : ∀{Γc Γ a}{B : TyP Γc} → fC {ℓ} Γ (ft a iU) → iP {ℓ} (Γ ▶P El a) B → iP Γ (a ⇒P B)

iSP (iEl {a = a})         = ft a iU
iSP (iΠ̂P {T = T} {B} x ι) = iSP ι
iSP (i⇒P x ι)             = iSP ι

nat : Set _
nat = fC {zero}{∙c ▶c U} (∙ ▶S U ▶P El vz ▶P vz ⇒P El vz) (ivz iU)

nzero : nat
nzero = fPs (fPz iEl)

nsucc : nat → nat
nsucc = λ n → fPz (i⇒P n iEl)

concᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃc {ℓ} Δc
concᵃ {ℓ} {Δc} Δ = {!!}

conᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δ)
conᵃ = {!!}
