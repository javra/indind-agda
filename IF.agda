{-# OPTIONS --rewriting #-}

module IF where

open import Lib hiding (id; _∘_)

infixl 3 _▶c_ _▶P_
infixr 5 _$S_ _⇒P_

data TyS : Set₁ where
  U  : TyS
  Π̂S : (T : Set) → (T → TyS) → TyS

data SCon : Set₁ where
  ∙c   : SCon
  _▶c_ : SCon → TyS → SCon

data Var : SCon → TyS → Set₁ where
  vvz : ∀{Γc B} → Var (Γc ▶c B) B
  vvs : ∀{Γc B B'} → Var Γc B → Var (Γc ▶c B') B

data Tm (Γc : SCon) : TyS → Set₁ where
  var  : ∀{A} → Var Γc A → Tm Γc A
  _$S_ : ∀{T B} → Tm Γc (Π̂S T B) → (α : T) → Tm Γc (B α)

data TyP (Γc : SCon) : Set₁ where
  El   : Tm Γc U → TyP Γc
  Π̂P   : (T : Set) → (T → TyP Γc) → TyP Γc
  _⇒P_ : Tm Γc U → TyP Γc → TyP Γc

data Con (Γc : SCon) : Set₁ where
  ∙    : Con Γc
  _▶P_ : Con Γc → (B : TyP Γc) → Con Γc

-- No terms in the empty context
Tm∙c : ∀{B} → Tm ∙c B → ⊥
Tm∙c (var ())
Tm∙c (t $S α) = Tm∙c t

-- Non dependent, recursive functions
_⇒̂S_ : Set → TyS → TyS
T ⇒̂S A = Π̂S T (λ _ → A)

_⇒̂P_ : ∀{Γc} → Set → TyP Γc → TyP Γc
T ⇒̂P A = Π̂P T (λ _ → A)

-- ▶S
vz : ∀{Γc}{A} → Tm (Γc ▶c A) A
vz = var vvz

vs : ∀{Γc}{A}{B} → Tm Γc A → Tm (Γc ▶c B) A
vs (var x)  = var (vvs x)
vs (t $S α) = vs t $S α

Twk : ∀{Γc}{B} → TyP Γc → TyP (Γc ▶c B)
Twk (El a)   = El (vs a)
Twk (Π̂P T B) = Π̂P T λ τ → Twk (B τ)
Twk (a ⇒P A) = vs a ⇒P Twk A

_▶S_ : ∀{Γc}(Γ : Con Γc)(B : TyS) → Con (Γc ▶c B)
∙        ▶S B = ∙
(Γ ▶P A) ▶S B = (Γ ▶S B) ▶P Twk A

-- Substitution calculus
data Sub : SCon → SCon → Set₁ where
  ε   : ∀{Γc} → Sub Γc ∙c
  _,_ : ∀{Γc}{Δc}{B} → Sub Γc Δc → Tm Γc B → Sub Γc (Δc ▶c B)

_[_]T : ∀{Γc}{Δc} → TyP Δc → Sub Γc Δc → TyP Γc
_[_]t : ∀{Γc}{Δc}{B} → Tm Δc B → Sub Γc Δc → Tm Γc B

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

π₁ : ∀{Γc}{Δc}{B} → Sub Γc (Δc ▶c B) → Sub Γc Δc
π₁ (δ , t) = δ

π₂ : ∀{Γc}{Δc}{B} → Sub Γc (Δc ▶c B) → Tm Γc B
π₂ (δ , t) = t

_∘_ : ∀{Γc}{Δc}{Ωc} → Sub Ωc Δc → Sub Γc Ωc → Sub Γc Δc
ε        ∘ γc = ε
(δc , x) ∘ γc = (δc ∘ γc) , (x [ γc ]t)

wk : ∀{Γc}{Δc}{B} → Sub Γc Δc → Sub (Γc ▶c B) Δc
wk ε        = ε
wk (δc , t) = wk δc , vs t

wkβ : ∀{Γc Δc Ωc B}{δc : Sub Γc Δc}{γc : Sub Ωc Γc}{t : Tm Ωc B} → wk δc ∘ (γc , t) ≡ δc ∘ γc
wkβ {δc = ε}                    = refl
wkβ {δc = δc , var x}{γc}       = (λ δc₁ → δc₁ , (var x [ γc ]t)) & wkβ
wkβ {δc = δc , (x $S α)}{γc}{t} = _,_ (wk δc ∘ (γc , _)) & vs[,]t (x $S α) t γc ◾ (λ δc₁ → δc₁ , ((x [ γc ]t) $S α)) & wkβ

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
