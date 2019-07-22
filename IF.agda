{-# OPTIONS --rewriting #-}

module IF where

open import Lib hiding (id; _∘_)

infixl 3 _▶c_ _▶P_
infixr 5 _$S_ _⇒P_
infixl 7 _[_]T
infixl 8 _[_]tP
infixl 8 _[_]t

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
  _$S_ : ∀{T B} → Tm Γc (Π̂S T B) → (τ : T) → Tm Γc (B τ)

data TyP (Γc : SCon) : Set₁ where
  El   : Tm Γc U → TyP Γc
  Π̂P   : (T : Set) → (T → TyP Γc) → TyP Γc
  _⇒P_ : Tm Γc U → TyP Γc → TyP Γc

data Con (Γc : SCon) : Set₁ where
  ∙    : Con Γc
  _▶P_ : Con Γc → TyP Γc → Con Γc

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

-- Substitution calculus
data Sub : SCon → SCon → Set₁ where
  ε   : ∀{Γc} → Sub Γc ∙c
  _,_ : ∀{Γc Δc B} → Sub Γc Δc → Tm Γc B → Sub Γc (Δc ▶c B)

_[_]t : ∀{Γc Δc B} → Tm Δc B → Sub Γc Δc → Tm Γc B
var vvz      [ δ , t ]t = t
var (vvs a)  [ δ , t ]t = var a [ δ ]t
(a $S α)     [ δ ]t     = (a [ δ ]t) $S α

_[_]T : ∀{Γc Δc} → TyP Δc → Sub Γc Δc → TyP Γc
Π̂P T u   [ δ ]T = Π̂P T (λ α → u α [ δ ]T)
El u     [ δ ]T = El (u [ δ ]t)
(a ⇒P B) [ δ ]T = (a [ δ ]t) ⇒P (B [ δ ]T)

_[_]C : ∀{Γc Δc} → Con Δc → Sub Γc Δc → Con Γc
∙        [ σ ]C = ∙
(Γ ▶P A) [ σ ]C = (Γ [ σ ]C) ▶P (A [ σ ]T)

vs[,]t : ∀{Γc Δc A B}(s : Tm Δc A)(t : Tm Γc B)(δ : Sub Γc Δc) → (vs s) [ δ , t ]t ≡ (s [ δ ]t)
vs[,]t (var vvz) t δ     = refl
vs[,]t (var (vvs x)) t δ = refl
vs[,]t (s $S α) t δ      = happly2 _$S_ (vs[,]t s t δ) α
{-# REWRITE vs[,]t #-}

_∘_ : ∀{Γc}{Δc}{Ωc} → Sub Ωc Δc → Sub Γc Ωc → Sub Γc Δc
ε        ∘ γc = ε
(δc , t) ∘ γc = (δc ∘ γc) , (t [ γc ]t)

wk : ∀{Γc}{Δc}{B} → Sub Γc Δc → Sub (Γc ▶c B) Δc
wk ε        = ε
wk (δc , t) = wk δc , vs t

wkβ : ∀{Γc Δc Ωc B}{δc : Sub Γc Δc}{γc : Sub Ωc Γc}{t : Tm Ωc B} → wk δc ∘ (γc , t) ≡ δc ∘ γc
wkβ {δc = ε}                    = refl
wkβ {δc = δc , var x}{γc}       = (λ δc₁ → δc₁ , (var x [ γc ]t)) & wkβ
wkβ {δc = δc , (x $S α)}{γc}{t} = _,_ (wk δc ∘ (γc , _)) & vs[,]t (x $S α) t γc ◾ (λ δc₁ → δc₁ , ((x [ γc ]t) $S α)) & wkβ
{-# REWRITE wkβ #-}

id : ∀{Γ} → Sub Γ Γ
id {∙c}     = ε
id {Γ ▶c B} = wk id , vz

idl : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → id ∘ δ ≡ δ
idl ε       = refl
idl (δ , x) = (λ δ₁ → δ₁ , x) & (idl δ)
{-# REWRITE idl #-}

π₁ : ∀{Γc}{Δc}{B} → Sub Γc (Δc ▶c B) → Sub Γc Δc
π₁ (δ , t) = δ

π₂ : ∀{Γc}{Δc}{B} → Sub Γc (Δc ▶c B) → Tm Γc B
π₂ (δ , t) = t

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

[wk]t : ∀{Γ Δ B B'}(δ : Sub Γ Δ) → (t : Tm Δ B) → t [ wk {B = B'} δ ]t ≡ vs (t [ δ ]t)
[wk]t ε       (var ())
[wk]t (δ , x) (var vvz)      = refl
[wk]t (δ , x) (var (vvs t))  = [wk]t δ (var t)
[wk]t δ       (t $S α)       = happly2 _$S_ ([wk]t δ t) _
{-# REWRITE [wk]t #-}

[id]t : ∀{Γ}{B} → (t : Tm Γ B) → t [ id ]t ≡ t
[id]t (var vvz)     = refl
[id]t (var (vvs t)) = vs & [id]t (var t)
[id]t (t $S α)      = happly2 _$S_ ([id]t t) _
{-# REWRITE [id]t #-}

[id]T : ∀{Γ} → (A : TyP Γ) → A [ id ]T ≡ A
[id]T (Π̂P T x) = Π̂P T & ext λ α → [id]T (x α)
[id]T (El x)   = El & [id]t x
[id]T (x ⇒P A) = (_⇒P_ & [id]t x) ⊗ [id]T A
{-# REWRITE [id]T #-}

idr : ∀{Γ}{Δ} → (δ : Sub Γ Δ) → δ ∘ id ≡ δ
idr ε       = refl
idr (δ , x) = _,_ & idr δ ⊗ [id]t x
{-# REWRITE idr #-}

[][]t : ∀{Γ Δ Ω B}(t : Tm Ω B)(δ : Sub Γ Δ)(γ : Sub Δ Ω) → t [ γ ]t [ δ ]t ≡ t [ γ ∘ δ ]t
[][]t (t $S α)      δ ε       = happly2 _$S_ ([][]t t δ ε) _
[][]t (var vvz)     δ (γ , x) = refl
[][]t (var (vvs t)) δ (γ , x) = [][]t (var t) δ γ
[][]t (t $S α)      δ (γ , x) = happly2 _$S_ ([][]t t δ (γ , x)) _
{-# REWRITE [][]t #-}

[][]T : ∀{Γ Δ Ω} → (A : TyP Ω) (δ : Sub Γ Δ)(γ : Sub Δ Ω) → A [ γ ]T [ δ ]T ≡ A [ γ ∘ δ ]T
[][]T {Γ} {Δ} {Ω} (Π̂P T B) δ γ = Π̂P T & ext λ α → [][]T (B α) δ γ
[][]T {Γ} {Δ} {Ω} (El a) δ γ   = El & [][]t a δ γ
[][]T {Γ} {Δ} {Ω} (t ⇒P A) δ γ = _⇒P_ & [][]t t δ γ ⊗ [][]T A δ γ
{-# REWRITE [][]T #-}

ass : ∀{Γ Δ Ω Σ}{δ : Sub Γ Δ}{γ : Sub Δ Ω}{ι : Sub Ω Σ} → (ι ∘ γ) ∘ δ ≡ ι ∘ (γ ∘ δ)
ass {δ = δ}{γ}{ε}     = refl
ass {δ = δ}{γ}{ι , t} = (λ x → x , (t [ γ ∘ δ ]t)) & ass {δ = δ} {γ} {ι}

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

_▶S_ : ∀{Γc}(Γ : Con Γc)(B : TyS) → Con (Γc ▶c B)
_▶S_ {Γc} Γ B = Γ [ wk id ]C

-- Point substitution calculus
data VarP {Γc} : Con Γc → TyP Γc → Set₁ where
  vvzP : ∀{Γ A} → VarP (Γ ▶P A) A
  vvsP : ∀{Γ A B} → VarP Γ A → VarP (Γ ▶P B) A

data TmP {Γc}(Γ : Con Γc) : TyP Γc → Set₁ where
  varP : ∀{A} → VarP Γ A → TmP Γ A
  _$P_ : ∀{a A} → TmP Γ (a ⇒P A) → TmP Γ (El a) → TmP Γ A
  _$̂P_ : ∀{T A} → TmP Γ (Π̂P T A) → (τ : T) → TmP Γ (A τ)

data SubP {Γc} : Con Γc → Con Γc → Set₁ where
  εP   : ∀{Γ} → SubP Γ ∙
  _,P_ : ∀{Γ Δ A} → SubP Γ Δ → TmP Γ A → SubP Γ (Δ ▶P A)

vzP : ∀{Γc Γ A} → TmP {Γc} (Γ ▶P A) A
vzP = varP vvzP

vsP : ∀{Γc Γ A A'} → TmP {Γc} Γ A → TmP (Γ ▶P A') A
vsP (varP x) = varP (vvsP x)
vsP (f $P t) = vsP f $P vsP t
vsP (f $̂P τ) = vsP f $̂P τ

wkP : ∀{Γc}{Γ Δ : Con Γc}{A} → SubP Γ Δ → SubP (Γ ▶P A) Δ
wkP εP        = εP
wkP (σP ,P t) = wkP σP ,P vsP t

idP : ∀{Γc}{Γ : Con Γc} → SubP Γ Γ
idP {Γ = ∙}      = εP
idP {Γ = Γ ▶P A} = wkP idP ,P vzP

{-∘P : ∀{Γc Δc Σc}{Γ : Con Γc}{Δ : Con Δc}{Σ : Con Σc}
      {σ}(σP : SubP σ Δ Σ){δ}(δP : SubP δ Γ Δ) → SubP (σ ∘ δ) Γ Σ
∘P εP δP = εP
∘P {σ = σ} (σP ,P tP) δP = {!!} ,P {!!}-}

{-_,S_ : ∀{Γc}{Γ Δ : Con Γc}(σP : SubP Γ Δ){B}(t : Tm Γc B) → SubP  Γ (Δ ▶S B)
_,S_ {Δ = ∙}      σP                t = εP
_,S_ {Δ = Δ ▶P A} (σP ,P tP) t = (σP ,S t) ,P tP -- coe (TmP _ & [][]T A (σ , t) (wk id)) tP
-}

_[_]tP : ∀{Γc}{Γ Δ : Con Γc}{A}(tP : TmP Δ A)(σP : SubP Γ Δ) → TmP Γ A
varP vvzP     [ σP ,P tP ]tP = tP
varP (vvsP v) [ σP ,P tP ]tP = varP v [ σP ]tP
(tP $P sP)    [ σP ]tP       = (tP [ σP ]tP) $P (sP [ σP ]tP)
(tP $̂P τ)     [ σP ]tP       = (tP [ σP ]tP) $̂P τ

-- no point terms in the empty point context
TmP∙ : ∀{Γc A} → TmP {Γc} ∙ A → ⊥
TmP∙ (varP ())
TmP∙ (tP $P sP) = TmP∙ tP
TmP∙ (tP $̂P τ)  = TmP∙ tP

[wkP]tP : ∀{Γc}{Γ Δ : Con Γc}{A A'}(σP : SubP Γ Δ)(tP : TmP Δ A)
            → tP [ wkP {A = A'} σP ]tP ≡ vsP (tP [ σP ]tP)
[wkP]tP εP         tP              = ⊥-elim (TmP∙ tP)
[wkP]tP (σP ,P tP) (varP vvzP)     = refl
[wkP]tP (σP ,P tP) (varP (vvsP v)) = [wkP]tP σP (varP v)
[wkP]tP (σP ,P _)  (tP $P sP)      = happly2 _$P_ ([wkP]tP _ tP) _
                                     ◾ (_$P_ (vsP (tP [ _ ]tP))) & [wkP]tP _ sP
[wkP]tP (σP ,P _)  (tP $̂P τ)       = happly2 _$̂P_ ([wkP]tP _ tP) τ
{-# REWRITE [wkP]tP #-}

[idP]tP : ∀{Γc}{Γ : Con Γc}{A}{tP : TmP Γ A} → tP [ idP ]tP ≡ tP
[idP]tP {tP = varP vvzP}     = refl
[idP]tP {tP = varP (vvsP v)} = vsP & [idP]tP {tP = varP v}
[idP]tP {tP = tP $P sP}      = happly2 _$P_ ([idP]tP {tP = tP}) _
                               ◾ _$P_ tP & [idP]tP
[idP]tP {tP = tP $̂P τ}       = happly2 _$̂P_ [idP]tP τ
{-# REWRITE [idP]tP #-}


--TODO complete calculus here
