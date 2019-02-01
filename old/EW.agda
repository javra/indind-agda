{-# OPTIONS --rewriting #-}
module EW where

open import Lib hiding (id; _∘_)
open import Syntax using (PS; P; S)
import IFSyntax as S
open import IFA

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 3 _▶_

record Con : Set₁ where
  field
    Ec : S.SCon
    E  : S.Con Ec
    wc : {γc : Ec ᴬc} → (γ : (E ᴬC) γc) → S.SCon
    w  : {γc : Ec ᴬc} → (γ : (E ᴬC) γc) → S.Con (wc γ)

record TyS (Γ : Con) : Set₁ where
  module Γ = Con Γ
  field
    w  : {γc : Γ.Ec ᴬc} → (γ : (Γ.E ᴬC) γc) → S.TyS

record TyP (Γ : Con) : Set₁ where
  module Γ = Con Γ
  field
    E : S.TyP Γ.Ec
    w : {γc : Γ.Ec ᴬc} → (γ : (Γ.E ᴬC) γc) → (α : (E ᴬP) γc) → S.TyP (Γ.wc γ)

record TmS (Γ : Con) (A : TyS Γ) : Set₁ where
  module Γ = Con Γ
  module A = TyS A
  field
    E : S.Tm Γ.Ec S.U
    w : {γc : Γ.Ec ᴬc} → (γ : (Γ.E ᴬC) γc) → (α : (E ᴬt) γc) → S.Tm (Γ.wc γ) (A.w γ)

--record TmP (Γ : Con) (A : TyP Γ) : Set₁ where
--  module Γ = Con Γ
--  module A = TyS A
--  field

record Sub (Γ : Con) (Δ : Con) : Set₁ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    Ec : S.Sub Γ.Ec Δ.Ec
    E  : ∀{γc} → (Γ.E ᴬC) γc → (Δ.E ᴬC) ((Ec ᴬs) γc) --name?
    wc : ∀{γc}{γ : (Γ.E ᴬC) γc} → S.Sub (Γ.wc γ) (Δ.wc {γc = (Ec ᴬs) γc} (E γ))
 --   w  : ∀{γc}{γ : (Γ.E ᴬC) γc}{α} → ((Γ.w γ) ᴬC) α → (Δ.w (E γ) ᴬC) ((wc ᴬs) α) --name?

∙ : Con
∙ = record { Ec = S.∙c ; E = S.∙ ; wc = λ _ → S.∙c ; w = λ _ → S.∙ }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S A = record { Ec = Γ.Ec S.▶c S.U ;
                  E = Γ.E S.▶S S.U ;
                  wc = λ { (γ , T) → (Γ.wc γ) S.▶c (T S.⇒̂S A.w γ) } ;
                  w =  λ { (γ , T) → (Γ.w γ) S.▶S (T S.⇒̂S A.w γ)} }
  where
    module Γ = Con Γ
    module A = TyS A

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { Ec = Γ.Ec ;
                  E = Γ.E S.▶P A.E ;
                  wc = λ { (γ , α) → Γ.wc γ } ;
                  w = λ { (γ , α) → Γ.w γ S.▶P A.w γ α } }
  where
    module Γ = Con Γ
    module A = TyP A

U : {Γ : Con} → TyS Γ
U {Γ} = record { w = λ γ → S.U }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { E = S.El a.E ;
                    w = λ { γ (lift α) → S.El (a.w γ α) } }
  where
    module Γ = Con Γ
    module a = TmS a

ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS a B = record { w = λ {γc} γ → S.Π̂S ((a.E ᴬt) γc) (λ α → B.w (γ , lift α)) }
  where
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} → (a : TmS Γ U) → (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP a B = record { E = a.E S.⇒P B.E ;
                  w = λ {γc} γ β → S.Π̂P ((a.E ᴬt) γc) (λ τ → a.w γ τ S.⇒P (B.w (γ , lift τ) (β τ))) }
  where
    module a = TmS a
    module B = TyP B

--app : ∀{k Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a) k} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS t = record { E = t.E ;
                  w = λ { (γ , lift υ) τ → t.w γ τ S.$S υ} }
  where
    module t = TmS t

--appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (t : TmP Γ (ΠS a B)) → TmP (Γ ▶P El a) B
--appP t = ?

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B δ = record { w = λ γ → B.w (δ.E γ) }
  where
    module B = TyS B
    module δ = Sub δ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A δ = record { E = A.E S.[ δ.Ec ]T ;
                      w = λ {γc} γ α →  A.w (δ.E γ) α S.[ δ.wc ]T }
--                      w = λ {γc} γ α →  A.w (δ.E γ) (coe ([]TᴬS {A = A.E}{δ = δ.Ec} γc) α) S.[ δ.wc ]T }
  where
    module A = TyP A
    module δ = Sub δ

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS a σ = record { E = a.E S.[ σ.Ec ]t ;
                      w = λ γ α → a.w (σ.E γ) α S.[ σ.wc ]t }
  where
    module a = TmS a
    module σ = Sub σ

--_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
--_[_]tP a σ = ?

U[] : ∀{Γ Δ}{δ : Sub Γ Δ} → U [ δ ]TS ≡ U
U[] = refl

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U} → (El a [ σ ]TP) ≡ (El (coe (TmS Γ & (U[] {δ = σ})) (a [ σ ]tS)))
El[] = refl

--ΠS[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U}{B : TyS (Δ ▶P El a)}
--      → ((ΠS a B) [ σ ]TS) ≡ (ΠS (a [ σ ]tS) (B [ σ ^ El a ]TS))
--ΠS[] = ?

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { Ec = S.id ;
                  E  = λ γ → γ;
                  wc = S.id }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { Ec = σ.Ec S.∘ δ.Ec ;
                 E = λ γ → σ.E (δ.E γ) ;
                 wc = σ.wc S.∘ δ.wc }
  where
    module σ = Sub σ
    module δ = Sub δ

ε : ∀{Γ} → Sub Γ ∙
ε = record { Ec = S.ε ;
             E = λ _ → lift tt ;
             wc = S.ε }

_,s_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : TyS Δ} → TmS Γ (A [ σ ]TS) → Sub Γ (Δ ▶S A)
σ ,s t = record { Ec = σ.Ec S., t.E ;
                  E = λ {γc} γ → σ.E γ , (t.E ᴬt) γc;
                  wc = λ {γc}{γ} → σ.wc S., {!t.w!} } -- this is a problem, seems like we do need λ̂ in the end
  where
    module σ = Sub σ
    module t = TmS t

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ = record { Ec = S.π₁ σ.Ec ;
                 E = λ γ → ₁ (σ.E γ) ;
                 wc = S.π₁ σ.wc }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { Ec = σ.Ec ;
                 E = λ γ → ₁ (σ.E γ) ;
                 wc = σ.wc }
  where
    module σ = Sub σ

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S σ = record { E = S.π₂ σ.Ec ;
                 w = λ γ τ → {!!} }
  where
    module σ = Sub σ

{-
[id]T : ∀{k Γ}{A : Ty Γ k} → A [ id ]T ≡ A
[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
        → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T

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

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

vs : ∀{k Γ}{A B : Ty Γ k} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs x = x [ wk ]t

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


-- Universe
--------------------------------------------------------------------------------

postulate


-- Inductive functions
--------------------------------------------------------------------------------
postulate



  app[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))
-}
