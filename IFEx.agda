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

-- Both curC and curS are equivalences of types, I think
-- These operations are transformations on arbitrary algebras
curc : ∀{ℓ}{Δc}(f : ic Δc → Set ℓ) → _ᵃc {ℓ} Δc
curS : ∀{ℓ}{B}(f : iS B → Set ℓ) → _ᵃS {ℓ} B
curC : ∀{ℓ}{Δc : SCon}{Δ : Con Δc}(f : ∀ {Δc} → Con Δc → ic Δc → Set ℓ)(fSs : ∀ Δc (Δ : Con Δc) B i → f Δ i → f (Δ ▶S B) (ivs i)) → _ᵃC Δ (curc (f Δ))
curP : ∀{ℓ}{Δc}{A}(f : ic Δc → Set ℓ) → _ᵃP A (curc f)

curc {ℓ}{∙c}      f = lift tt
curc {ℓ}{Δc ▶c B} f = curc (λ i → f (ivs i)) , curS λ i → f (ivz i)

curS {ℓ}{U} f      = f iU
curS {ℓ}{Π̂S T B} f = λ α → curS {ℓ} λ i → f (iΠ̂S α i)

curC {ℓ} {∙c} {Δ} f fSs = {!!}
curC {ℓ} {Δc ▶c U} {Δ} f fSs = {!!}
curC {ℓ} {Δc ▶c Π̂S T x} {Δ} f fSs = {!!}

curP = {!!}

--Defining the initial algebra
data iP {ℓ}{Γc} : ∀(Γ : Con Γc) → TyP Γc → Set ℓ
data fC {ℓ : Level} : ∀{Γc}(Γ : Con Γc) → ic Γc → Set ℓ

iSP : ∀{ℓ : Level}{Γc : SCon}{Γ : Con Γc}{A : TyP Γc} → iP {ℓ} Γ A → ic Γc

data fC {ℓ : Level}  where
  fSs : ∀{Γc}{Γ : Con Γc}{B i} → fC {ℓ} Γ i → fC (Γ ▶S B) (ivs i)
  fPs : ∀{Γc}{Γ : Con Γc}{A i} → fC {ℓ} Γ i → fC (Γ ▶P A) i
  fPz : ∀{Γc}{Γ : Con Γc}{A}(ι : iP {ℓ} (Γ ▶P A) A) → fC (Γ ▶P A) (iSP ι)

data iP {ℓ}{Γc} where
  iEl : ∀{Γ a} → iP Γ (El a)
  iΠ̂P : ∀{Γ T B}(α : T) → iP {ℓ} Γ (B α) → iP Γ (Π̂P T B)
  i⇒P : ∀{Γ a B} → fC {ℓ} Γ (ft a iU) → iP {ℓ} (Γ ▶P El a) B → iP Γ (a ⇒P B)

iSP (iEl {a = a})         = ft a iU
iSP (iΠ̂P {T = T} {B} x ι) = iSP ι
iSP (i⇒P x ι)             = iSP ι

--some examples
nat : Set
nat = fC (∙ ▶S U ▶P El vz ▶P vz ⇒P El vz) (ivz iU)

nzero : nat
nzero = fPs (fPz iEl)

nsucc : nat → nat
nsucc = λ n → fPz (i⇒P n iEl)

vec : nat → Set
vec = λ n → fC (∙ ▶S Π̂S nat (λ _ → U) ▶P El (vz $S nzero) ▶P Π̂P nat λ m → (vz $S m) ⇒P El (vz $S nsucc m)) (ivz (iΠ̂S n iU))

vzero : vec nzero
vzero = fPs (fPz iEl)

vcons : ∀ n → vec n → vec (nsucc n)
vcons n v = fPz (iΠ̂P n (i⇒P v iEl))

concᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃc {ℓ} Δc
concᵃ Δ = curc (fC Δ)

conᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δ)
conᵃ ∙ = lift tt
conᵃ (Δ ▶S B) = {!!}
conᵃ (Δ ▶P A) = {!!} , {!!}
