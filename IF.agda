{-# OPTIONS --rewriting #-}

module IF where

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
data Var : SCon → TyS → Set₁
data Tm : SCon → TyS → Set₁

data TyP where
  Π̂P   : ∀{Γ}(T : Set) → (T → TyP Γ) → TyP Γ
  El   : ∀{Γ} → Tm Γ U → TyP Γ
  _⇒P_ : ∀{Γ} → Tm Γ U → TyP Γ → TyP Γ

data Var where
  vvz : ∀{Γ}{A} → Var (Γ ▶c A) A
  vvs : ∀{Γ}{A}{B} → Var Γ A → Var (Γ ▶c B) A

data Tm where
  var  : ∀{Γ}{A} → Var Γ A → Tm Γ A
  _$S_ : ∀{Γ}{T}{B} → Tm Γ (Π̂S T B) → (α : T) → Tm Γ (B α)

vz : ∀{Γ}{A} → Tm (Γ ▶c A) A
vz = var vvz

vs : ∀{Γ}{A}{B} → Tm Γ A → Tm (Γ ▶c B) A
vs (var x)  = var (vvs x)
vs (t $S α) = vs t $S α

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

var vvz      [ δ , t ]t = t
var (vvs a)  [ δ , t ]t = var a [ δ ]t
(a $S α)     [ δ ]t     = (a [ δ ]t) $S α

vs[,]t : ∀{Γ}{Δ}{A B}(s : Tm Δ A)(t : Tm Γ B)(δ : Sub Γ Δ) → (vs s) [ δ , t ]t ≡ (s [ δ ]t)
vs[,]t (var vvz) t δ     = refl
vs[,]t (var (vvs x)) t δ = refl
vs[,]t (s $S α) t δ      = happly2 _$S_ (vs[,]t s t δ) α

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
wkβ {δ = ε}                  = refl
wkβ {δ = δ , var x} {γ}      = (λ δ₁ → δ₁ , (var x [ γ ]t)) & wkβ
wkβ {δ = δ , (x $S α)}{γ}{t} = _,_ (wk δ ∘ (γ , _)) & vs[,]t (x $S α) t γ ◾ (λ δ₁ → δ₁ , ((x [ γ ]t) $S α)) & wkβ

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

[wk] : ∀{Γ Δ B B'}(δ : Sub Γ Δ) → (t : Tm Δ B) → t [ wk {B = B'} δ ]t ≡ vs (t [ δ ]t)
[wk] ε       (var ())
[wk] ε       (t $S α)       = happly2 _$S_ ([wk] ε t) _
[wk] (δ , x) (var vvz)      = refl
[wk] (δ , x) (var (vvs t))  = [wk] δ (var t)
[wk] (δ , x) (t $S α)       = happly2 _$S_ ([wk] (δ , x) t) _

[id]T : ∀{Γ} → (A : TyP Γ) → A [ id ]T ≡ A
[id]t : ∀{Γ}{B} → (t : Tm Γ B) → t [ id ]t ≡ t

[id]T (Π̂P T x) = Π̂P T & ext λ α → [id]T (x α)
[id]T (El x)   = El & [id]t x
[id]T (x ⇒P A) = (_⇒P_ & [id]t x) ⊗ [id]T A

[id]t (var vvz)     = refl
[id]t (var (vvs t)) = [wk] id (var t) ◾ vs & [id]t (var t)
[id]t (t $S α)      = happly2 _$S_ ([id]t t) _

idr : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → δ ∘ id ≡ δ
idr ε       = refl
idr (δ , x) = _,_ & idr δ ⊗ [id]t x

[][]T : ∀{Γ Δ Ω} → (A : TyP Ω) (δ : Sub Γ Δ)(γ : Sub Δ Ω) → A [ γ ]T [ δ ]T ≡ A [ γ ∘ δ ]T
[][]t : ∀{Γ Δ Ω B}(t : Tm Ω B)(δ : Sub Γ Δ)(γ : Sub Δ Ω) → t [ γ ]t [ δ ]t ≡ t [ γ ∘ δ ]t

[][]T {Γ} {Δ} {Ω} (Π̂P T B) δ γ = Π̂P T & ext λ α → [][]T (B α) δ γ
[][]T {Γ} {Δ} {Ω} (El a) δ γ   = El & [][]t a δ γ
[][]T {Γ} {Δ} {Ω} (t ⇒P A) δ γ = _⇒P_ & [][]t t δ γ ⊗ [][]T A δ γ

[][]t (t $S α)      δ ε       = happly2 _$S_ ([][]t t δ ε) _
[][]t (var vvz)     δ (γ , x) = refl
[][]t (var (vvs t)) δ (γ , x) = [][]t (var t) δ γ
[][]t (t $S α)      δ (γ , x) = happly2 _$S_ ([][]t t δ (γ , x)) _

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
