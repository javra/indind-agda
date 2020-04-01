{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module EWRSgRec where

open import Lib hiding (id; _∘_)
open import II using (PS; P; S)
import IF as S
open import IFA
open import IFD

infixl 7 _[_]TS
infixl 7 _[_]TP
infixl 7 _[_]T
infix  6 _∘_
infixl 8 _[_]tS
infixl 8 _[_]tP
infixl 8 _[_]t
infixl 5 _,tS_
infixl 5 _,tP_
infixl 5 _,t_
infixl 3 _▶_
infixl 3 _▶S_
infixl 3 _▶P_

record Con : Set₂ where
  field
    ᴬ   : Set₁
    Ec  : S.SCon
    E   : S.Con Ec

record TyS (Γ : Con) : Set₃ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set₁

record TyP (Γ : Con) : Set₃ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set
    E   : S.TyP Γ.Ec

Ty : (Γ : Con) (k : PS) → Set₃
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (B : TyS Γ) : Set₃ where
  module Γ = Con Γ
  module B = TyS B
  field
    ᴬ   : (γ : Γ.ᴬ) → B.ᴬ γ
    E   : S.Tm Γ.Ec S.U

record TmP (Γ : Con) (A : TyP Γ) : Set₃ where
  module Γ = Con Γ
  module A = TyP A
  field
    ᴬ   : (γ : Γ.ᴬ) → A.ᴬ γ
    E   : ∀{γc} → _ᵃC {zero} Γ.E γc → (A.E ᵃP) γc

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₃
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    ᴬ   : Γ.ᴬ → Δ.ᴬ
    Ec  : S.Sub Γ.Ec Δ.Ec
    E   : ∀{γc} → _ᵃC {zero} Γ.E γc → (Δ.E ᵃC) ((Ec ᵃs) γc)

∙ : Con
∙ = record { ᴬ   = Lift (suc zero) ⊤ ;
             Ec  = S.∙c ;
             E   = S.∙ }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S B = record { ᴬ   = Σ Γ.ᴬ B.ᴬ ;
                  Ec  = Γ.Ec S.▶c S.U ;
                  E   = Γ.E S.▶S S.U }
  where
    module Γ = Con Γ
    module B = TyS B
    
_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  Ec  = Γ.Ec ;
                  E   = Γ.E S.▶P A.E }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { ᴬ   = λ γ → Set }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { ᴬ   = λ γ → a.ᴬ γ ;
                    E   = S.El a.E }
  where
    module Γ = Con Γ
    module a = TmS a

ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { ᴬ   = λ γ → (α : a.ᴬ γ) → B.ᴬ (γ , α) }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} → (a : TmS Γ U) → (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP a B = record { ᴬ   = λ γ → (α : a.ᴬ γ) → B.ᴬ (γ , α) ;
                  E   = a.E S.⇒P B.E }
  where
    module a = TmS a
    module B = TyP B

Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {a = a}{B} t = record { ᴬ   = λ { (γ , α) → t.ᴬ γ α } ;
                             E   = t.E }
  where
    module a = TmS a
    module B = TyS B
    module t = TmS t

appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (t : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
appP {a = a}{B} t = record { ᴬ   = λ { (γ , α) → t.ᴬ γ α } ;
                             E   = λ { (γ , α) → t.E γ α } }
  where
    module a = TmS a
    module B = TyP B
    module t = TmP t

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { ᴬ   = λ γ → B.ᴬ (σ.ᴬ γ) }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { ᴬ   = λ γ → A.ᴬ (σ.ᴬ γ) ;
                      E   = A.E S.[ σ.Ec ]T }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                E   = a.E S.[ σ.Ec ]t }
  where
    module A = TyS A
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                E   = λ γ → a.E (σ.E γ) }
  where
    module A = TyP A
    module a = TmP a
    module σ = Sub σ

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} = _[_]tP
_[_]t {S} = _[_]tS

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ᴬ   = λ γ → γ ;
                  Ec  = S.id ;
                  E   = λ γc → γc }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { ᴬ   = λ γ → σ.ᴬ (δ.ᴬ γ) ;
                 Ec  = σ.Ec S.∘ δ.Ec ;
                 E   = λ γ → σ.E (δ.E γ) }
  where
    module σ = Sub σ
    module δ = Sub δ

ε : ∀{Γ} → Sub Γ ∙
ε = record { ᴬ   = λ _ → lift tt ;
             Ec  = S.ε ;
             E   = λ γ → lift tt }

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){B : TyS Δ} → TmS Γ (B [ σ ]TS) → Sub Γ (Δ ▶S B)
σ ,tS t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                   Ec  = σ.Ec S., t.E ;
                   E   = λ γ → σ.E γ }
  where
    module σ = Sub σ
    module t = TmS t

_,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
_,tP_ σ {A} t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                         Ec  = σ.Ec ;
                         E   = λ γ → σ.E γ , t.E γ }
  where
    module σ = Sub σ
    module A = TyP A
    module t = TmP t

_,t_ : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,t_ {P} = _,tP_
_,t_ {S} = _,tS_

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 Ec  = S.π₁ σ.Ec ;
                 E   = λ γ → σ.E γ }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 Ec  = σ.Ec ;
                 E   = λ γ → ₁ (σ.E γ) }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P}{A = A} = π₁P {A = A}
π₁ {S}        = π₁S

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           E   = S.π₂ σ.Ec }
  where
    module σ = Sub σ

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P {A = A} σ ]TP)
π₂P {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           E   = λ γ → ₂ (σ.E γ) }
  where
    module A = TyP A
    module σ = Sub σ

π₂ : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {k} σ ]T)
π₂ {P} {A = A} = π₂P {A = A}
π₂ {S}         = π₂S

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk {k} = π₁ {k} id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk {k} ]T)
vz = π₂ id

vsS : ∀{k Γ}{A : TyS Γ}{B : Ty Γ k} → TmS Γ A → TmS (Γ ▶ B) (A [ wk {k} ]TS)
vsS {k} t = t [ wk {k} ]tS

vsP : ∀{k Γ}{A : TyP Γ}{B : Ty Γ k} → TmP Γ A → TmP (Γ ▶ B) (A [ wk {k} ]TP)
vsP {k} t = t [ wk {k} ]tP

-- First kind: What is the resulting kind? Second kind: Along what kind are we weakening?
vs : ∀{k l Γ}{A : Ty Γ k}{B : Ty Γ l} → Tm Γ A → Tm (Γ ▶ B) (A [ wk {l} ]T)
vs {P}{l} t = vsP {l} t
vs {S}{l} t = vsS {l} t
{-
{-
-- Congruence Lemmas

TyS≡ : {Γ : Con}
    {w₀ w₁ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → Set → S.TyS}
    (w₂ : (λ {γc} → w₀ {γc}) ≡ w₁)
  → _≡_ {A = TyS Γ} (record { w = w₀ }) (record { w = w₁ })
TyS≡ refl = refl

TyPw≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)}
    (E₂ : E₀ ≡ E₁)
  → ({γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₀ ᵃP) γc) → S.TyP (Con.wc Γ γc γ))
  ≡ ({γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₁ ᵃP) γc) → S.TyP (Con.wc Γ γc γ))
TyPw≡ refl = refl

coeTyPw≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)} (E₂ : E₀ ≡ E₁)
    {w₀ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₀ ᵃP) γc) → S.TyP (Con.wc Γ γc γ)}
    {w₁ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₁ ᵃP) γc) → S.TyP (Con.wc Γ γc γ)}
    (w₂ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₀ ᵃP) γc) → w₀ γ α ≡ w₁ γ (coe (happly (_ᵃP & E₂) γc) α))
    {γc : _} {γ : (Con.E Γ ᵃC) γc} {α : _}
  → coe (TyPw≡ {Γ = Γ} E₂) w₀ γ α ≡ w₁ γ α
coeTyPw≡ refl w₂ = w₂ _ _
    
TyP≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)}
    (E₂ : E₀ ≡ E₁)
    {w₀ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₀ ᵃP) γc) → S.TyP (Con.wc Γ γc γ)}
    {w₁ : {γc : Con.Ec Γ ᵃc} → (γ : (Con.E Γ ᵃC) γc) → (α : (E₁ ᵃP) γc) → S.TyP (Con.wc Γ γc γ)}
    (w₂ : (λ {γc} → w₀ {γc}) ≡[ TyPw≡ {Γ = Γ} E₂ ]≡ (λ {γc} → w₁ {γc}))
  → _≡_ {A = TyP Γ} (record { E = E₀ ; w = w₀ }) (record { E = E₁ ; w = w₁ })
TyP≡ refl refl = refl

-- Proofs of the Substitution Laws

U[] : ∀{Γ Δ}{δ : Sub Γ Δ} → U [ δ ]TS ≡ U
U[] = refl

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U} → (El a [ σ ]TP) ≡ (El (coe (TmS Γ & (U[] {δ = σ})) (a [ σ ]tS)))
El[] = {!!} --refl

[id]T : ∀{k Γ}{A : Ty Γ k} → A [ id ]T ≡ A
[id]T {P}{Γ}{A} = TyP≡ (S.[id]T (TyP.E A))
                     (exti (λ γc → ext λ γ → ext λ α → coeTyPw≡ {Γ}
                       (S.[id]T (TyP.E A)) {w₀ = λ γ₁ α₁ → TyP.w A γ₁ α₁ S.[ S.id ]T} {w₁ = TyP.w A}
                       (λ γ' α' → S.[id]T (TyP.w A γ' α') ◾ (TyP.w A γ') & (coe_refl ⁻¹))))
[id]T {S}       = TyS≡ refl

--[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ} → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
--[][]T {P} = TyP≡ (S.[][]T _ _ _) {!!}
--[][]T {S} = TyS≡ refl

{-
idl   : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idr   : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
ass   : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

,∘    : ∀{k Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ k}{t : Tm Γ (A [ δ ]T)}
      → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
π₁β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → (π₁ (σ ,s t)) ≡ σ
πη    : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)}
      → (π₁ σ ,s π₂ σ) ≡ σ
εη    : ∀{Γ}{σ : Sub Γ ∙}
      → σ ≡ ε
π₂β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = {!!} --σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U}{B : TyS (Δ ▶P El a)}
      → ((ΠS a B) [ σ ]TS) ≡ (ΠS (a [ σ ]tS) (B [ σ ^ El a ]TS))
Π[] = ?


  app[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))
-}


-}
-}
