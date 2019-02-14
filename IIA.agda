module IIA where

open import Lib hiding (id; _∘_)
open import II using (PS;P;S)

infixl 7 _[_]TS
infixl 7 _[_]TP
infixl 7 _[_]T
infixl 5 _,tS_
infixl 5 _,tP_
infixl 5 _,t_
infix  6 _∘_
infixl 8 _[_]tS
infixl 8 _[_]tP
infixl 8 _[_]t
infixl 3 _▶S_
infixl 3 _▶P_
infixl 3 _▶_

record Con : Set₂ where
  constructor mkCon
  field
    _ᴬ  : Set₁
    ᴹ  : _ᴬ → _ᴬ → Set₁
open Con public

record TyS (Γ : Con) : Set₂ where
  constructor mkTy
  field
    _ᴬ  : Γ ._ᴬ → Set₁
    ᴹ  : ∀ {γ₀ γ₁} → Γ .ᴹ γ₀ γ₁ → γ₀ ᴬ → γ₁ ᴬ → Set₁
open TyS public

record TyP (Γ : Con) : Set₂ where
  constructor mkTy
  field
    _ᴬ  : Γ ._ᴬ → Set
    ᴹ  : ∀ {γ₀ γ₁} → Γ .ᴹ γ₀ γ₁ → _ᴬ γ₀ → _ᴬ γ₁ → Set
open TyP public

record TmS (Γ : Con)(A : TyS Γ) : Set₁ where
  constructor mkTm
  field
    _ᴬ  : (γ : Con._ᴬ Γ) → TyS._ᴬ A γ
    ᴹ  : ∀ {γ₀ γ₁}(γᴹ : Con.ᴹ Γ γ₀ γ₁) → TyS.ᴹ A γᴹ (_ᴬ γ₀) (_ᴬ γ₁)

record TmP (Γ : Con)(A : TyP Γ) : Set₁ where
  constructor mkTm
  field
    _ᴬ  : (γ : Con._ᴬ Γ) → TyP._ᴬ A γ
    ᴹ  : ∀ {γ₀ γ₁}(γᴹ : Con.ᴹ Γ γ₀ γ₁) → TyP.ᴹ A γᴹ (_ᴬ γ₀) (_ᴬ γ₁)

record Sub (Γ : Con)(Δ : Con) : Set₂ where
  constructor mkSub
  field
    _ᴬ  : Con._ᴬ Γ → Con._ᴬ Δ
    ᴹ  : {γ₀ γ₁ : Γ .Con._ᴬ}(γᴹ : Γ .ᴹ γ₀ γ₁) → Δ .ᴹ (_ᴬ γ₀) (_ᴬ γ₁)
open Sub public

∙ : Con
∙ = mkCon (Lift ⊤) (λ _ _ → Lift ⊤)

_▶S_ : ∀(Γ : Con) → TyS Γ → Con
Γ ▶S A = mkCon
  (Σ (Γ ._ᴬ) (A ._ᴬ))
  (λ γ₀ γ₁ → Σ (Γ .ᴹ (₁ γ₀) (₁ γ₁)) λ γᴹ → A .ᴹ γᴹ (₂ γ₀) (₂ γ₁))

_▶P_ : ∀(Γ : Con) → TyP Γ → Con
Γ ▶P A = mkCon
  (Σ (Γ ._ᴬ) (A ._ᴬ))
  (λ γ₀ γ₁ → Σ (Γ .ᴹ (₁ γ₀) (₁ γ₁)) λ γᴹ → A .ᴹ γᴹ (₂ γ₀) (₂ γ₁))

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS {Γ} {Δ} A σ =
  mkTy
    (λ γ → _ᴬ A (_ᴬ σ γ))
    (λ {γ₀}{γ₁} γᴹ α₀ α₁ → A .ᴹ (σ .ᴹ γᴹ) α₀ α₁)

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP {Γ} {Δ} A σ =
  mkTy
    (λ γ → _ᴬ A (_ᴬ σ γ))
    (λ {γ₀}{γ₁} γᴹ α₀ α₁ → A .ᴹ (σ .ᴹ γᴹ) α₀ α₁)

id : ∀{Γ} → Sub Γ Γ
id {Γ} =
  mkSub
    (λ γ → γ)
    (λ γᴹ → γᴹ)

_∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
_∘_ {Γ}{Δ}{Σ} σ δ =
  mkSub
    (λ γ → σ ._ᴬ (δ ._ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ (δ .ᴹ γᴹ))

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = _  -- inferable by ⊤ η

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : TyS Δ} → TmS Γ (A [ σ ]TS) → Sub Γ (Δ ▶S A)
_,tS_ {Γ} {Δ} σ {A} t =
  mkSub
    (λ γ → (σ ._ᴬ γ) , t .TmS._ᴬ γ)
    (λ {γ₀}{γ₁} γᴹ → (ᴹ σ γᴹ) , (t .TmS.ᴹ γᴹ))

_,tP_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : TyP Δ} → TmP Γ (A [ σ ]TP) → Sub Γ (Δ ▶P A)
_,tP_ {Γ} {Δ} σ {A} t =
  mkSub
    (λ γ → (σ ._ᴬ γ) , t .TmP._ᴬ γ)
    (λ {γ₀}{γ₁} γᴹ → (ᴹ σ γᴹ) , (t .TmP.ᴹ γᴹ))

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ =
  mkSub
    (λ γ → σ ._ᴬ γ .₁)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₁)

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ =
  mkSub
    (λ γ → σ ._ᴬ γ .₁)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₁)

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ} {Δ} {A} t σ =
  mkTm
    (λ γ → t .TmS._ᴬ (σ ._ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → t .TmS.ᴹ (σ .ᴹ γᴹ))

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ} {Δ} {A} t σ =
  mkTm
    (λ γ → t .TmP._ᴬ (σ ._ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → t .TmP.ᴹ (σ .ᴹ γᴹ))

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S {Γ} {Δ} {A} σ =
  mkTm
    (λ γ → σ ._ᴬ γ .₂)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₂)

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P σ ]TP)
π₂P {Γ} {Δ} {A} σ =
  mkTm
    (λ γ → σ ._ᴬ γ .₂)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₂)
{-
[id]TS : ∀{Γ}{A : Ty Γ k} → A [ id ]T ≡ A
[id]TS = refl
[id]T {S} = refl

[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
        → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
[][]T {P} = refl
[][]T {S} = refl

idl : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idl = refl

idr : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
idr = refl

ass : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

,∘ : ∀{k Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ k}{t : Tm Γ (A [ δ ]T)}
      → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
,∘ {P} = refl
,∘ {S} = refl

π₁β : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → (π₁ {k} (σ ,s t)) ≡ σ
π₁β {P} = refl
π₁β {S} = refl

πη : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)}
      → (π₁ σ ,s π₂ σ) ≡ σ
πη = refl

εη : ∀{Γ}{σ : Sub Γ ∙}
      → σ ≡ ε
εη = refl

π₂β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t
π₂β {P} = refl
π₂β {S} = refl

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk {k} = π₁ {k} id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk {k} ]T)
vz = π₂ id

vs : ∀{k l Γ}{A : Ty Γ k}{B : Ty Γ l} → Tm Γ A → Tm (Γ ▶ B) (A [ wk {l} ]T)
vs {k}{l} x = x [ wk {l} ]t

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk {k} ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ S
U {Γ} =
  mkTy
    (λ _ → Set₁)
    (λ _ A B → (A → B))

U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
U[] {Γ}{Δ}{σ} = refl

El : ∀{Γ}(a : Tm Γ U) → Ty Γ P
El {Γ} a =
  mkTy
    (λ γ → Lift (a .Tm._ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ α αᴹ → a .Tm.ᴹ γᴹ (α .lower) ≡ αᴹ .lower)

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (coe (Tm Γ & (U[] {σ = σ})) (a [ σ ]t)))
El[] = refl

-- Inductive functions
--------------------------------------------------------------------------------

Π : ∀{k Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} {Γ} a B =
  mkTy
    (λ γ → (x : a .Tm._ᴬ γ) → B ._ᴬ (γ , lift x))
    (λ {γ₀}{γ₁} γᴹ f₀ f₁ → (x : a .Tm._ᴬ γ₀)
       → B .ᴹ (γᴹ , refl) (f₀ x) (f₁ (a .Tm.ᴹ γᴹ x)))

Π {S} {Γ} a B =
  mkTy
    (λ γ → (x : a .Tm._ᴬ γ) → B ._ᴬ (γ , lift x))
    (λ {γ₀}{γ₁} γᴹ f₀ f₁ → (x : a .Tm._ᴬ γ₀)
       → B .ᴹ (γᴹ , refl) (f₀ x) (f₁ (a .Tm.ᴹ γᴹ x)))

Π[] :
  {k : PS} {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ {S} (U {Δ})} {B : Ty
  (_▶_ {P} Δ (El {Δ} a)) k} → _≡_ {i} {Ty Γ k} (_[_]T {k} {Γ}
  {Δ} (Π {k} {Δ} a B) σ) (Π {k} {Γ} (tr {i} {j} {Ty Γ S} (Tm Γ
  {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})
  (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)) (tr {i} {i} {Ty Γ P} (λ x →
  Ty (_▶_ {P} Γ x) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ}
  (tr {i} {j} {Ty Γ S} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ}
  {U {Γ}} (U[] {Γ} {Δ} {σ}) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))}
  (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ}
  {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ
  (El {Δ} a)))))
Π[] {P} = refl
Π[] {S} = refl

app : ∀{k Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a) k} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app {P} {Γ} {a} {B} t =
  mkTm
    (λ {(γ , α) → t .Tm._ᴬ γ (α .lower)})
    (λ { {γ₀ , α₀}{γ₁ , α₁}(γᴹ , αᴹ) →
       J (λ x p → ᴹ B (γᴹ , p) (t .Tm._ᴬ γ₀ (α₀ .lower)) (t .Tm._ᴬ γ₁ x))
         (t .Tm.ᴹ γᴹ (α₀ .lower))
         αᴹ})
app {S} {Γ} {a} {B} t =
  mkTm
    (λ {(γ , α) → t .Tm._ᴬ γ (α .lower)})
    (λ { {γ₀ , α₀}{γ₁ , α₁}(γᴹ , αᴹ) →
       J (λ x p → ᴹ B (γᴹ , p) (t .Tm._ᴬ γ₀ (α₀ .lower)) (t .Tm._ᴬ γ₁ x))
         (t .Tm.ᴹ γᴹ (α₀ .lower))
         αᴹ})

app[] :
     {k : PS} {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ {S} (U {Δ})} {B : Ty (_▶_
     {P} Δ (El {Δ} a)) k} {t : Tm Δ {k} (Π {k} {Δ} a B)} → _≡_ {j} {Tm (_▶_
     {P} Γ (El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ
     {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U
     {Δ}} a σ)))) {k} (tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_ {P} Γ z) k)
     {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set
     j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
     (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k}
     {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B
     (_^_ {P} {Γ} {Δ} σ (El {Δ} a))))} (tr2 {i} {i} {j} {Ty Γ P} {λ z → Ty
     (_▶_ {P} Γ z) k} (λ A → Tm (_▶_ {P} Γ A) {k}) {_[_]T {P} {Γ} {Δ} (El
     {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)}
     {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T
     {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ}
     {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) {_[_]T {k} {_▶_ {P} Γ (_[_]T {P}
     {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El
     {Δ} a))} {tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_ {P} Γ z) k) {_[_]T {P}
     {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U
     {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ
     {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t
     {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P}
     Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P}
     {Γ} {Δ} σ (El {Δ} a)))} refl (_[_]t {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ}
     (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} {B} (app {k} {Δ} {a} {B} t) (_^_
     {P} {Γ} {Δ} σ (El {Δ} a)))) (app {k} {Γ} {coe {j} {Tm Γ {S} (_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set
     j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
     (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)} {tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_
     {P} Γ z) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ
     {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j}
     {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[]
     {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a})
     (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El
     {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El {Δ} a)))} (tr {i} {j} {Ty Γ k} (Tm Γ
     {k}) {_[_]T {k} {Γ} {Δ} (Π {k} {Δ} a B) σ} {Π {k} {Γ} (coe {j} {Tm Γ
     {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j}
     {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[]
     {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)) (tr {i} {i} {Ty Γ P} (λ
     z → Ty (_▶_ {P} Γ z) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe
     {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_
     {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ}
     {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ}
     {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)}
     {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El {Δ} a))))} (Π[] {k}
     {Γ} {Δ} {σ} {a} {B}) (_[_]t {k} {Γ} {Δ} {Π {k} {Δ} a B} t σ)))
app[] {P} = refl
app[] {S} = refl
-}
