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
curS : ∀{ℓ}{B}(f : iS B → Set ℓ) → _ᵃS {ℓ} B
curS {ℓ}{U} f      = f iU
curS {ℓ}{Π̂S T B} f = λ α → curS {ℓ} λ i → f (iΠ̂S α i)

curc : ∀{ℓ}{Δc}(f : ic Δc → Set ℓ) → _ᵃc {ℓ} Δc
curc {ℓ}{∙c}      f = lift tt
curc {ℓ}{Δc ▶c B} f = curc (λ i → f (ivs i)) , curS λ i → f (ivz i)

curC : ∀{ℓ}{Δc}(f : Con Δc → ic Δc → Set ℓ)(iP : Con Δc → TyP Δc → Set ℓ)(iSP : ∀{Γ A} → iP Γ A → ic Δc)
  (fz : ∀{Γ A}(ιP : iP (Γ ▶P A) A) → iP Γ A → f (Γ ▶P A) (iSP ιP))
  (fs : ∀{Γ A ι} → f Γ ι → f (Γ ▶P A) ι)
  → (Γ : Con Δc) → _ᵃC Γ (curc (f Γ))
curP : ∀{ℓ}{Δc}(f : Con Δc → ic Δc → Set ℓ)(iP : Con Δc → TyP Δc → Set ℓ)(iSP : ∀{Γ A} → iP Γ A → ic Δc)
  (fz : ∀{Γ A}(ιP : iP (Γ ▶P A) A) → iP Γ A → f (Γ ▶P A) (iSP ιP))
  (fs : ∀{Γ A ι} → f Γ ι → f (Γ ▶P A) ι)
  → (Γ : Con Δc) → (A : TyP Δc) → _ᵃP A (curc (f (Γ ▶P A)))

curC {Δc = ∙c} f iP iSP fz fs ∙ = lift tt
curC {Δc = ∙c} f iP iSP fz fs (Γ ▶P El x) = {!!}
curC {Δc = ∙c} f iP iSP fz fs (Γ ▶P Π̂P T x) = {!!}
curC {Δc = ∙c} f iP iSP fz fs (Γ ▶P x ⇒P B) = {!!}
curC {Δc = Δc ▶c x} f iP iSP fz fs Γ = {!!}

{-curP {Δc = ∙c} f iP iSP fz fs Γ (El a) = ⊥-elim (Tm∙c a)
curP {Δc = ∙c} f iP iSP fz fs Γ (Π̂P T B) = λ τ → curP f iP iSP fz fs Γ (B τ)
curP {Δc = ∙c} f iP iSP fz fs Γ (A ⇒P B) = λ α → curP f iP iSP fz fs Γ B
curP {Δc = Δc ▶c B} f iP iSP fz fs Γ (El a) = {!!}
curP {Δc = Δc ▶c B} f iP iSP fz fs Γ (Π̂P T C) = {!!}
curP {Δc = Δc ▶c B} f iP iSP fz fs Γ (a ⇒P A) = λ α → curP {_}{Δc} (λ Δ ι → f (Δ ▶S B) (ivs ι)) {!!} {!!} {!!} {!!} {!!} {!!}-}

curP f iP iSP fz fs Γ (El a) = {!!}
curP f iP iSP fz fs Γ (Π̂P T B) = {!!}
curP f iP iSP fz fs Γ (a ⇒P A) = λ α → curP (λ Δ ι → f {!!} {!!}) {!!} {!!} {!!} {!!} Γ A

--Defining the initial algebra
--iP are the indices (LHS) of a point constructor
--fC Γc Γ ι contains the points for index ι for context Γ
--iSP gives the index of the point constructor result, given its input
data iP {ℓ}{Γc} : ∀(Γ : Con Γc) → TyP Γc → Set ℓ
data fC {ℓ : Level} (Γc : SCon) : Con Γc → ic Γc → Set ℓ

iSP : ∀{ℓ : Level}{Γc : SCon}{Γ : Con Γc}{A : TyP Γc} → iP {ℓ} Γ A → ic Γc

data fC {ℓ : Level} (Γc : SCon) where
  fPz : ∀{Γ : Con Γc}{A}(ι : iP {ℓ} (Γ ▶P A) A) → fC Γc (Γ ▶P A) (iSP ι)
  fPs : ∀{Γ : Con Γc}{A i} → fC {ℓ} Γc Γ i → fC Γc (Γ ▶P A) i

data iP {ℓ}{Γc} where
  iEl : ∀{Γ a} → iP Γ (El a)
  iΠ̂P : ∀{Γ T B}(α : T) → iP {ℓ} Γ (B α) → iP Γ (Π̂P T B)
  i⇒P : ∀{Γ a B} → fC {ℓ} Γc Γ (ft a iU) → iP {ℓ} (Γ ▶P El a) B → iP Γ (a ⇒P B)

iSP (iEl {a = a})         = ft a iU
iSP (iΠ̂P {T = T} {B} x ι) = iSP ι
iSP (i⇒P x ι)             = iSP ι

--some examples
nat : Set
nat = fC (∙c ▶c U) (∙ ▶P El vz ▶P vz ⇒P El vz) (ivz iU)

nzero : nat
nzero = fPs (fPz iEl)

nsucc : nat → nat
nsucc = λ n → fPz (i⇒P n iEl)

vec : Set → nat → Set
vec A = λ n → fC (∙c ▶c Π̂S nat (λ _ → U)) (∙ ▶P El (vz $S nzero) ▶P Π̂P A λ a → (Π̂P nat λ m → (vz $S m) ⇒P El (vz $S nsucc m))) (ivz (iΠ̂S n iU))

vzero : {A : Set} → vec A nzero
vzero = fPs (fPz iEl)

vcons : ∀ {A : Set} a n → vec A n → vec A (nsucc n)
vcons a n v = fPz (iΠ̂P a (iΠ̂P n (i⇒P v iEl)))

concᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃc {ℓ} Δc
concᵃ Δ = curc (fC _ Δ)

conᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δ)
conᵃ ∙ = lift tt
conᵃ (Δ ▶P A) = {!!} , {!!} -- morally fPs (conᵃ Δ) , fPz (conPᵃ Δ A)
