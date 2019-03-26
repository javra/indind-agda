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
-- For sort types  (is B → Set)                            ≃ (B ᵃS)
-- For sort ctxts  (ic Δc → Set)                           ≃ (Δc ᵃc)
-- For contexts    (certain sections of (f : ic Δc → Set)) ≃ (Δ ᵃC) "f"
-- For point types (???)                                   ≃ (A ᵃP) 
curS : ∀{ℓ}{B}(f : iS B → Set ℓ) → _ᵃS {ℓ} B
curS {ℓ}{U} f      = f iU
curS {ℓ}{Π̂S T B} f = λ α → curS {ℓ} λ i → f (iΠ̂S α i)

curc : ∀{ℓ}{Δc}(f : ic Δc → Set ℓ) → _ᵃc {ℓ} Δc
curc {ℓ}{∙c}      f = lift tt
curc {ℓ}{Δc ▶c B} f = curc (λ i → f (ivs i)) , curS λ i → f (ivz i)

curP : ∀{ℓ Δc}(f : Con Δc → ic Δc → Set ℓ)
  (fz : ∀{Γ A}(ιP : iP (f (Γ ▶P A)) A) → f (Γ ▶P A) (iSP ιP))(fs : ∀{Γ A ι} → f Γ ι → f (Γ ▶P A) ι)
  → ∀ Γ A → (φ : (ιP : iP (f (Γ ▶P A)) A) → f (Γ ▶P A) (iSP ιP)) → (A ᵃP) (curc (f Γ))
curP f fz fs Γ (El a) φ = {!!}
curP f fz fs Γ (Π̂P T B) φ = {!!}
curP f fz fs Γ (a ⇒P A) φ = λ α → curP f fz fs Γ A λ ιP → {!!}

{-
fsfoo : ∀{ℓ Δc}(f : Con Δc → ic Δc → Set ℓ)(fs : ∀{Γ A ι} → f Γ ι → f (Γ ▶P A) ι)
  → (Δ : Con Δc) → (A₀ A₁ : TyP Δc) → (ι : ic Δc) → f (Δ ▶P A₁) ι → f (Δ ▶P A₀ ▶P A₁) ι
fsfoo f fs Δ A₀ (El a) ι x = {!!}
fsfoo f fs Δ A₀ (Π̂P T A) ι x = {!!}
fsfoo f fs Δ A₀ (a ⇒P A₁) ι x = {!!}

curC : ∀{ℓ Δc}(f : Con Δc → ic Δc → Set ℓ)(iP : Con Δc → TyP Δc → Set ℓ)(iSP : ∀{Γ A} → iP Γ A → ic Δc)
  (fz : ∀{Γ A} ιP → f (Γ ▶P A) (iSP ιP))(fs : ∀{Γ A ι} → f Γ ι → f (Γ ▶P A) ι)
  (iEl : ∀{Γ a} → iP Γ (El a))(iΠ̂P : ∀{Γ T B}(α : T)→ iP Γ (B α) → iP Γ (Π̂P T B))
  (i⇒P : ∀{Γ a B} → f Γ (ft a iU) → iP (Γ ▶P El a) B → iP Γ (a ⇒P B))
  → (Γ : Con Δc) → _ᵃC Γ (curc (f Γ))
curC f iP iSP fz fs iEl iΠ̂P i⇒P ∙        = lift tt
curC f iP iSP fz fs iEl iΠ̂P i⇒P (Γ ▶P A) = {!!} {-curC (λ Δ ι → f (Δ ▶P A) ι) iP iSP
                                             (λ ιP → fs (fz ιP)) {!!}
                                             iEl iΠ̂P (λ x ιP → i⇒P {!!} ιP) Γ ,
                                           curP f iP iSP fz fs Γ A {!!}-}
-}

data f {ℓ}{Γc} : Con Γc → ic Γc → Set ℓ  where
  fz : ∀{Γ : Con Γc}{A}(ι : iP {ℓ} (f (Γ ▶P A)) A) → f (Γ ▶P A) (iSP ι)
  fs : ∀{Γ : Con Γc}{A i} → f {ℓ} Γ i → f (Γ ▶P A) i

concᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃc {ℓ} Δc
concᵃ Δ = curc (f Δ)

conᵃ : ∀{ℓ}{Δc}(Δ : Con Δc) → _ᵃC {ℓ} Δ (concᵃ Δ)
conᵃ Δ = {!!} -- curC fC iP iSP fPz fPs iEl iΠ̂P i⇒P Δ

--some examples
nat : Set
nat = f {_} {∙c ▶c U} (∙ ▶P El vz ▶P vz ⇒P El vz) (ivz iU)

nzero : nat
nzero = fs (fz iEl)

nsucc : nat → nat
nsucc = λ n → fz (i⇒P n iEl)

vec : Set → nat → Set
vec A = λ n → f {_} {∙c ▶c Π̂S nat (λ _ → U)} (∙ ▶P El (vz $S nzero) ▶P Π̂P A λ a → (Π̂P nat λ m → (vz $S m) ⇒P El (vz $S nsucc m))) (ivz (iΠ̂S n iU))

vzero : {A : Set} → vec A nzero
vzero = fs (fz iEl)

vcons : ∀ {A : Set} a n → vec A n → vec A (nsucc n)
vcons a n v = fz (iΠ̂P a (iΠ̂P n (i⇒P v iEl)))
