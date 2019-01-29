{-# OPTIONS --rewriting #-}

module IFSyntax where

open import Lib hiding (id; _∘_)

--{-# BUILTIN REWRITE _≡_ #-}

data SCon : Set₁
data TyS : Set₁

infixl 3 _▶c_
infixl 3 _▶S_
infixl 3 _▶P_
infixr 5 _$S_
infixr 5 _⇒P_


data SCon where
  ∙c   : SCon
  _▶c_ : SCon → TyS → SCon

data TyS where
  U  : TyS
  Π̂S : (T : Set) → (T → TyS) → TyS

data TyP : SCon → Set₁
data Tm : SCon → TyS → Set₁

data TyP where
  Π̂P   : ∀{Γ}(T : Set) → (T → TyP Γ) → TyP Γ
  El   : ∀{Γ} → Tm Γ U → TyP Γ
  _⇒P_ : ∀{Γ} → Tm Γ U → TyP Γ → TyP Γ

data Tm where
  vz   : ∀{Γ}{A} → Tm (Γ ▶c A) A
  vs   : ∀{Γ}{A}{B} → Tm Γ A → Tm (Γ ▶c B) A
  _$S_ : ∀{Γ}{T}{B} → Tm Γ (Π̂S T B) → (α : T) → Tm Γ (B α)

postulate vs$S : ∀{Γ T}{α : T}{B : T → TyS}{B'} → (t : Tm Γ (Π̂S T B)) → vs {B = B'} (t $S α) ≡ vs t $S α
{-# REWRITE vs$S #-}

data Con : SCon → Set₁ where
  ∙    : Con ∙c
  _▶S_ : ∀{Γ} → Con Γ → (A : TyS) → Con (Γ ▶c A)
  _▶P_ : ∀{Γ} → Con Γ → TyP Γ → Con Γ

_⇒̂S_ : Set → TyS → TyS
T ⇒̂S A = Π̂S T (λ _ → A)

_⇒̂P_ : ∀{Γ} → Set → TyP Γ → TyP Γ
T ⇒̂P A = Π̂P T (λ _ → A)

-- Substitution calculus
data Sub : SCon → SCon → Set₁ where
  ε   : ∀{Γ} → Sub Γ ∙c
  _,_ : ∀{Γ}{Δ}{B} → Sub Γ Δ → Tm Γ B → Sub Γ (Δ ▶c B)

_[_]T : ∀{Γ}{Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]t : ∀{Γ}{Δ}{B} → Tm Δ B → Sub Γ Δ → Tm Γ B

Π̂P T u   [ δ ]T = Π̂P T (λ α → u α [ δ ]T)
El u     [ δ ]T = El (u [ δ ]t)
(a ⇒P B) [ δ ]T = (a [ δ ]t) ⇒P (B [ δ ]T)

vz       [ δ , t ]t = t
vs a     [ δ , t ]t = a [ δ ]t
(a $S α) [ δ ]t     = (a [ δ ]t) $S α

π₁ : ∀{Γ}{Δ}{B} → Sub Γ (Δ ▶c B) → Sub Γ Δ
π₁ (δ , t) = δ

π₂ : ∀{Γ}{Δ}{B} → Sub Γ (Δ ▶c B) → Tm Γ B
π₂ (δ , t) = t

_∘_ : ∀{Γ}{Δ}{Ω} → Sub Ω Δ → Sub Γ Ω → Sub Γ Δ
ε       ∘ γ = ε
(δ , x) ∘ γ = (δ ∘ γ) , (x [ γ ]t)

wk : ∀{Γ}{Δ}{B} → Sub Γ Δ → Sub (Γ ▶c B) Δ
wk ε       = ε
wk (δ , t) = wk δ , vs t

wkβ : ∀{Γ Δ Ω B}{δ : Sub Γ Δ}{γ : Sub Ω Γ}{t : Tm Ω B} → wk δ ∘ (γ , t) ≡ δ ∘ γ
wkβ {δ = ε}         = refl
wkβ {δ = δ , x} {γ} = (λ δ₁ → δ₁ , (x [ γ ]t)) & wkβ

id : ∀{Γ} → Sub Γ Γ
id {∙c}     = ε
id {Γ ▶c B} = wk id , vz

idl : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → id ∘ δ ≡ δ
idl ε       = refl
idl (δ , x) = (λ δ₁ → δ₁ , x) & (wkβ ◾ idl δ)

_^_ : ∀{Γ Δ} → Sub Γ Δ → (B : TyS) → Sub (Γ ▶c B) (Δ ▶c B)
δ ^ B = wk δ , vz

id^ : ∀{Γ B} → id {Γ} ^ B ≡ id
id^ = refl

π₁β : ∀{Γ Δ B}{δ : Sub Γ Δ}{t : Tm Γ B} → π₁ (δ , t) ≡ δ
π₁β = refl

π₂β : ∀{Γ Δ B}{δ : Sub Γ Δ}{t : Tm Γ B} → π₂ (δ , t) ≡ t
π₂β = refl

πβ : ∀{Γ Δ B}{δ : Sub Γ (Δ ▶c B)} → (π₁ δ , π₂ δ) ≡ δ
πβ {δ = δ , x} = refl

vs$S' : ∀{Γ T}{α : T}{B : T → TyS}{B'} → (t : Tm Γ (Π̂S T B)) → vs {B = B'} (t $S α) ≡ vs t $S α
vs$S' {Γ} {T} {α} {B} {B'} t = refl

[wk] : ∀{Γ Δ B B'}(δ : Sub Γ Δ) → (t : Tm Δ B) → t [ wk {B = B'} δ ]t ≡ vs (t [ δ ]t)
[wk] {Γ = Γ}{B' = B'} ε (t $S α)       = ((λ x → coe x ((t [ ε ]t) $S α)) & (const& ((_$S_ & [wk] {Γ = Γ}{B' = B'} ε t)) ⁻¹)
                                         ◾ apd (λ f → f α) (_$S_ & [wk] ε t))
[wk]                  (δ , x) vz       = refl
[wk]                  (δ , x) (vs t)   = [wk] δ t
[wk] {Γ = Γ}{B' = B'} (δ , x) (t $S α) = ((λ y → coe y ((t [ wk δ , vs x ]t) $S α)) & (const& (_$S_ & [wk] {Γ = Γ}{B' = B'} (δ , x) t) ⁻¹)
                                         ◾ apd (λ f → f α) (_$S_ & [wk] (δ , x) t))

[id]T : ∀{Γ} → (A : TyP Γ) → A [ id ]T ≡ A
[id]t : ∀{Γ}{B} → (t : Tm Γ B) → t [ id ]t ≡ t

[id]T (Π̂P T x) = Π̂P T & ext λ α → [id]T (x α)
[id]T (El x)   = El & [id]t x
[id]T (x ⇒P A) = (_⇒P_ & [id]t x) ⊗ [id]T A

[id]t vz       = refl
[id]t (vs t)   = [wk] id t ◾ vs & [id]t t
[id]t (t $S α) = (λ x → coe x ((t [ id ]t) $S α)) & (const& (_$S_ & [id]t t) ⁻¹) ◾ apd (λ f → f α) (_$S_ & [id]t t)

idr : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → δ ∘ id ≡ δ
idr ε       = refl
idr (δ , x) = _,_ & idr δ ⊗ [id]t x

[][]T : ∀{Γ Δ Ω} → (A : TyP Ω) (δ : Sub Γ Δ)(γ : Sub Δ Ω) → A [ γ ]T [ δ ]T ≡ A [ γ ∘ δ ]T
[][]t : ∀{Γ Δ Ω B}(t : Tm Ω B)(δ : Sub Γ Δ)(γ : Sub Δ Ω) → t [ γ ]t [ δ ]t ≡ t [ γ ∘ δ ]t

[][]T {Γ} {Δ} {Ω} (Π̂P T B) δ γ = Π̂P T & ext λ α → [][]T (B α) δ γ
[][]T {Γ} {Δ} {Ω} (El a) δ γ   = El & [][]t a δ γ
[][]T {Γ} {Δ} {Ω} (t ⇒P A) δ γ = _⇒P_ & [][]t t δ γ ⊗ [][]T A δ γ

[][]t (t $S α) δ ε       = (λ x → coe x (((t [ ε ]t) [ δ ]t) $S α)) & (const& (_$S_ & [][]t t δ ε) ⁻¹)
                           ◾ apd (λ f → f α) (_$S_ & [][]t t δ ε)
[][]t vz δ (γ , x)       = refl
[][]t (vs t) δ (γ , x)   = [][]t t δ γ
[][]t (t $S α) δ (γ , x) = (λ y → coe y (((t [ γ , x ]t) [ δ ]t) $S α)) & (const& (_$S_ & [][]t t δ (γ , x)) ⁻¹)
                           ◾ apd (λ f → f α) (_$S_ & [][]t t δ (γ , x))

ass : ∀{Γ Δ Ω Σ}{δ : Sub Γ Δ}{γ : Sub Δ Ω}{ι : Sub Ω Σ} → (ι ∘ γ) ∘ δ ≡ ι ∘ (γ ∘ δ)
ass {ι = ε}     = refl
ass {ι = ι , x} = _,_ & ass ⊗ [][]t x _ _

εη : ∀{Γ} (δ : Sub Γ ∙c) → δ ≡ ε
εη ε = refl

,∘ : ∀{Γ Δ Ω}{δ : Sub Γ Δ}{γ : Sub Ω Γ}{B : TyS}{t : Tm Γ B} → ((δ , t) ∘ γ) ≡ (δ ∘ γ) , (t [ γ ]t)
,∘ = refl

El[] : ∀{Γ Δ}{δ : Sub Γ Δ}{a : Tm Δ U} → (El a) [ δ ]T ≡ El (a [ δ ]t)
El[] = refl

Π̂P[] : ∀{Γ Δ}{δ : Sub Γ Δ}{T}{A : T → TyP Δ} → (Π̂P T A) [ δ ]T ≡ Π̂P T λ α → A α [ δ ]T
Π̂P[] = refl

$S[] : ∀{Γ Δ}{δ : Sub Γ Δ}{T}{B}{t : Tm Δ (Π̂S T B)}{α} → (t $S α) [ δ ]t ≡ (t [ δ ]t) $S α
$S[] = refl

⇒P[] : ∀{Γ Δ}{δ : Sub Γ Δ}{a : Tm Δ U}{A : TyP Δ} → (a ⇒P A) [ δ ]T ≡ (a [ δ ]t) ⇒P (A [ δ ]T)
⇒P[] = refl
