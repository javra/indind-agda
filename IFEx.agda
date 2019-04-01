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

data iP {ℓ}{Γc}(fCΓ : ic Γc → Set ℓ) : TyP Γc → Set ℓ  where
  iEl : ∀{a} → iP fCΓ (El a)
  iΠ̂P : ∀{T B}(α : T) → iP {ℓ} fCΓ (B α) → iP fCΓ (Π̂P T B)
  i⇒P : ∀{a B} → fCΓ (ft a iU) → iP {ℓ} fCΓ B → iP fCΓ (a ⇒P B)

iSP : ∀{ℓ Γc A fCΓ} → iP {ℓ} fCΓ A → ic Γc
iSP (iEl {a = a}) = ft a iU
iSP (iΠ̂P _ ι)     = iSP ι
iSP (i⇒P _ ι)     = iSP ι

-- Both curC and curS are equivalences of types, I think
-- These operations are transformations on arbitrary algebras
-- For sort types  (iS B → Set)                            ≃ (B ᵃS)
-- For sort ctxts  (ic Δc → Set)                           ≃ (Δc ᵃc)
-- For contexts    (certain sections of (f : ic Δc → Set)) ≃ (Δ ᵃC) "f"
-- For point types (???)                                   ≃ (A ᵃP) 
curS : ∀{ℓ}{B}(f : iS B → Set ℓ) → _ᵃS {ℓ} B
curS {ℓ}{U} f      = f iU
curS {ℓ}{Π̂S T B} f = λ α → curS {ℓ} λ i → f (iΠ̂S α i)

curc : ∀{ℓ}{Δc}(f : ic Δc → Set ℓ) → _ᵃc {ℓ} Δc
curc {ℓ}{∙c}      f = lift tt
curc {ℓ}{Δc ▶c B} f = curc (λ i → f (ivs i)) , curS λ i → f (ivz i)

data f {ℓ}{Γc}(Ω : Con Γc) : Con Γc → ic Γc → Set ℓ  where
  fz : ∀{Γ : Con Γc}{A}(ι : iP {ℓ} (f Ω Ω) A) → f Ω (Γ ▶P A) (iSP ι)
  fs : ∀{Γ : Con Γc}{A i} → f {ℓ} Ω Γ i → f Ω (Γ ▶P A) i

curC : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (curc (f Δ Δ))
curC ∙ = lift tt
curC {Δc = ∙c} (Δ ▶P B) = {!!}
curC {Δc = Δc ▶c x} (Δ ▶P B) = {!!}

concᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃc {ℓ} Δc
concᵃ Δ = curc (f Δ Δ)

conᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δ)
conᵃ Δ = {!!}

--some examples
nat : Set
nat = f {_} {∙c ▶c U} (∙ ▶P vz ⇒P El vz ▶P El vz) (∙ ▶P vz ⇒P El vz ▶P El vz) (ivz iU)

nzero : nat
nzero = fz iEl

nsucc : nat → nat
nsucc = λ n → fs (fz (i⇒P n iEl))

vec : Set → nat → Set
vec A = λ n → f {_} {∙c ▶c Π̂S nat (λ _ → U)} (∙ ▶P El (vz $S nzero) ▶P Π̂P A λ a → (Π̂P nat λ m → (vz $S m) ⇒P El (vz $S nsucc m)))
  (∙ ▶P El (vz $S nzero) ▶P Π̂P A λ a → (Π̂P nat λ m → (vz $S m) ⇒P El (vz $S nsucc m))) (ivz (iΠ̂S n iU))

vzero : {A : Set} → vec A nzero
vzero = fs (fz iEl)

vcons : ∀ {A : Set} a n → vec A n → vec A (nsucc n)
vcons a n v = fz (iΠ̂P a (iΠ̂P n (i⇒P v iEl)))

Γc : SCon
Γc = ∙c ▶c U ▶c U

Γ : Con Γc
Γ = ∙ ▶P El (vs (vz)) ▶P El vz

SΓc : Γc ᵃc
SΓc = lift tt , f {zero} Γ Γ (ivs (ivz iU)) , f Γ Γ (ivz iU)

SΓ : (Γ ᵃC) SΓc
SΓ = lift tt , fs (fz iEl) , fz iEl
