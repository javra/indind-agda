module IFSyntax where

open import Lib hiding (id; _∘_)

data TCon : Set₁
data TyS : Set₁

infixl 3 _▶t_
infixl 3 _▶S_
infixl 3 _▶P_
infixr 5 _$S_
infixr 5 _⇒P_

data TCon where
  ∙t   : TCon
  _▶t_ : TCon → TyS → TCon

data TyS where
  U  : TyS
  Π̂S : (T : Set) → (T → TyS) → TyS

data TyP : TCon → Set₁
data Tm : TCon → TyS → Set₁

data TyP where
  Π̂P   : ∀{Γ}(T : Set) → (T → TyP Γ) → TyP Γ
  El   : ∀{Γ} → Tm Γ U → TyP Γ
  _⇒P_ : ∀{Γ} → Tm Γ U → TyP Γ → TyP Γ

data Tm where
  vz   : ∀{Γ}{A} → Tm (Γ ▶t A) A
  vs   : ∀{Γ}{A}{B} → Tm Γ A → Tm (Γ ▶t B) A
  _$S_ : ∀{Γ}{T}{B} → Tm Γ (Π̂S T B) → (α : T) → Tm Γ (B α)

data Con : TCon → Set₁ where
  ∙    : Con ∙t
  _▶S_ : ∀{Γ} → Con Γ → (A : TyS) → Con (Γ ▶t A)
  _▶P_ : ∀{Γ} → Con Γ → TyP Γ → Con Γ

_⇒̂S_ : Set → TyS → TyS
T ⇒̂S A = Π̂S T (λ _ → A)

_⇒̂P_ : ∀{Γ} → Set → TyP Γ → TyP Γ
T ⇒̂P A = Π̂P T (λ _ → A)

-- Substitution calculus
data Sub : TCon → TCon → Set₁ where
  ε   : ∀{Γ} → Sub Γ ∙t
  _,_ : ∀{Γ}{Δ}{B} → Sub Γ Δ → Tm Γ B → Sub Γ (Δ ▶t B)

_[_]T : ∀{Γ}{Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]t : ∀{Γ}{Δ}{B} → Tm Δ B → Sub Γ Δ → Tm Γ B

Π̂P T u   [ δ ]T = Π̂P T (λ α → u α [ δ ]T)
El u     [ δ ]T = El (u [ δ ]t)
(a ⇒P B) [ δ ]T = (a [ δ ]t) ⇒P (B [ δ ]T)

vz       [ δ , t ]t = t
vs a     [ δ , t ]t = a [ δ ]t
(a $S α) [ δ ]t     = (a [ δ ]t) $S α

π₁ : ∀{Γ}{Δ}{B} → Sub Γ (Δ ▶t B) → Sub Γ Δ
π₁ (δ , t) = δ

π₂ : ∀{Γ}{Δ}{B} → Sub Γ (Δ ▶t B) → Tm Γ B
π₂ (δ , t) = t

_∘_ : ∀{Γ}{Δ}{Ω} → Sub Ω Δ → Sub Γ Ω → Sub Γ Δ
ε       ∘ γ = ε
(δ , x) ∘ γ = (δ ∘ γ) , (x [ γ ]t)

wk : ∀{Γ}{Δ}{B} → Sub Γ Δ → Sub (Γ ▶t B) Δ
wk ε       = ε
wk (δ , t) = wk δ , vs t

id : ∀{Γ} → Sub Γ Γ
id {∙t}     = ε
id {Γ ▶t B} = wk id , vz

_^_ : ∀{Γ Δ} → Sub Γ Δ → (B : TyS) → Sub (Γ ▶t B) (Δ ▶t B)
δ ^ B = wk δ , vz

[wk] : ∀{Γ}{B} → (t : Tm Γ B) → t [ wk {B = B} (id {Γ}) ]t ≡ vs t
[wk] vz = refl
[wk] (vs t) = {!!}
[wk] (t $S α) = {!!}


[id]T : ∀{Γ} → (A : TyP Γ) → A [ id ]T ≡ A
[id]t : ∀{Γ}{B} → (t : Tm Γ B) → t [ id ]t ≡ t

[id]T (Π̂P T x) = Π̂P T & ext λ α → [id]T (x α)
[id]T (El x)   = El & [id]t x
[id]T (x ⇒P A) = (_⇒P_ & [id]t x) ⊗ [id]T A

[id]t vz       = refl
[id]t (vs t)   = {!!} ◾ vs & [id]t t
[id]t (t $S α) = (λ x → coe x ((t [ id ]t) $S α)) & (const& (_$S_ & [id]t t) ⁻¹) ◾ apd (λ f → f α) (_$S_ & [id]t t)

idr : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → δ ∘ id ≡ δ
idr {∙t} ε = refl
idr {∙t} (δ , x) = {!!}
idr {Γ ▶t x} δ = {!!}

idl : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → id ∘ δ ≡ δ
idl {∙t} ε = refl
idl {∙t} (δ , x) = {!!}
idl {Γ ▶t x} δ = {!!}
