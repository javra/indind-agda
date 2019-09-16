module IIA where

open import Lib hiding (id; _∘_)

data PS : Set where P S : PS

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 3 _▶_

Con : Set₂
Con = Set₁

Ty : Con → Set₂
Ty Γ = Γ → Set₁

Tm : ∀ Γ → Ty Γ → Set₁
Tm Γ A = (γ : Γ) → A γ

Sub : Con → Con → Set₁
Sub Γ Δ = Γ → Δ

∙ : Con
∙ = Lift _ ⊤

_▶_ : ∀(Γ : Con) → Ty Γ → Con
Γ ▶ A = Σ Γ λ γ → A γ 

_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
A [ σ ]T = λ γ → A (σ γ)

id : ∀{Γ} → Sub Γ Γ
id γ = γ

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = λ γ → σ (δ γ)

ε : ∀{Γ} → Sub Γ ∙
ε = λ γ → lift tt

_,s_ : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (_▶_ Δ A)
σ ,s t = λ γ → σ γ , t γ

π₁ : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (_▶_  Δ A) → Sub Γ Δ
π₁ σ γ = ₁ (σ γ)

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (_[_]T A σ)
t [ σ ]t = λ γ → t (σ γ)

π₂ : ∀{Γ Δ}{A : Ty Δ}(σ : Sub Γ (_▶_ Δ A)) → Tm Γ (_[_]T A (π₁ σ))
π₂ σ γ = ₂ (σ γ)

[id]T : ∀{Γ}{A : Ty Γ} → _[_]T A id ≡ A
[id]T = refl

[][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
          → _[_]T (_[_]T A δ) σ ≡ _[_]T A (δ ∘ σ)
[][]T = refl

idl : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idl = refl

idr : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
idr = refl

ass : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
        → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

,∘ : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ}{t : Tm Γ (_[_]T A δ)}
        → ((_,s_ δ {A} t) ∘ σ) ≡ (_,s_ (δ ∘ σ) (tr (Tm Σ) ([][]T {_}{_}{_}{A}{σ}{δ}) (_[_]t t σ)))
,∘ = refl

π₁β : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (_[_]T A σ)}
        → (π₁ (_,s_ σ {A} t)) ≡ σ
π₁β = refl

πη : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ (_▶_ Δ A)}
        → (_,s_ (π₁ σ) (π₂ σ)) ≡ σ
πη = refl

εη : ∀{Γ}{σ : Sub Γ ∙}
        → σ ≡ ε
εη = refl

π₂β   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (_[_]T A σ)}
        → π₂ {A = A} (_,s_ σ t) ≡ tr (λ σ → Tm Γ (_[_]T A σ)) (π₁β {A = A}{t = t} ⁻¹) t
π₂β = refl

wk : ∀{Γ}{A : Ty Γ} → Sub (_▶_ Γ A) Γ
wk = π₁ id

vz : ∀{Γ}{A : Ty Γ} → Tm (_▶_ Γ A) (_[_]T A wk)
vz = π₂ id

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (_▶_ Γ B) (_[_]T A wk)
vs x = _[_]t x wk

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (_▶_  Γ A)
<_> t = _,s_ id (tr (Tm _) ([id]T ⁻¹) t)

infix 4 <_>

_^_ : ∀{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (_▶_ Γ(_[_]T A σ)) (_▶_  Δ A)
_^_{Γ} {Δ} σ A = σ ∘ wk ,s vz {Γ} {A [ σ ]T}

infixl 5 _^_

U : ∀{Γ} → Ty Γ
U = λ _ → Set

U[] : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
U[] = refl

El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El a γ = Lift _ (a γ)

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (a [ σ ]t))
El[] = refl

Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
Π a B γ = (α : a γ) → B (γ , lift α)

Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}
      → (Π a B) [ σ ]T ≡ Π (a [ σ ]t) (B [ σ ^ El a ]T)
Π[] = refl

app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app t (γ , lift α) = t γ α

app[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}{t : Tm Δ (Π a B)}
          → (app t [ σ ^ El a ]t) ≡ app (t [ σ ]t)
app[] = refl

