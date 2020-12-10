{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}
module RedProp where

open import Lib hiding (id; _∘_)
open import StrictLib renaming (_,_ to _p,_)
import IFdep as S
open import IFAdep
open import IFPAdep
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

data PS : Set where
  P : PS
  S : PS

record Con : Set₂ where
  field
    ᴬ   : Set₁
    ᴹ   : ᴬ → ᴬ → Set₁
    ᴾᴬ  : Set₁
    Ec  : S.SCon
    E   : S.Con Ec
    wc  : ∀{γc}(γ : _ᵃC {zero} E γc) → S.SCon
    w   : ∀{γc}(γ : (E ᵃC) γc) → S.Con (wc γ)
    Rc  : ∀{γc}(γ : _ᵃC {zero} E γc)(γᴬ : ᴬ) → S.SCon
    R   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ) → S.Con (Rc γ γᴬ)

record TyS (Γ : Con) : Set₂ where
  no-eta-equality
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set₁
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set
    ᴾᴬ  : Γ.ᴾᴬ → Set₁
    w   : ∀(γc : _ᵃc {zero} Γ.Ec) → Set → S.TyS
    R   : ∀{γᴬ}(α : Set)(αᴬ : ᴬ γᴬ) → S.TyS

record TyP (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set₁
    ᴾᴬ  : Γ.ᴾᴬ → Prop
    E   : S.TyP Γ.Ec
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → (E ᵃP) γc → S.TyP (Γ.wc γ)
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}(α : (E ᵃP) γc)(αᴬ : ᴬ γᴬ) → S.TyP (Γ.Rc γ γᴬ)

Ty : (Γ : Con) (k : PS) → Set₂
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (B : TyS Γ) : Set₂ where
  module Γ = Con Γ
  module B = TyS B
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → B.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → B.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    ᴾᴬ  : (γᴾᴬ : Γ.ᴾᴬ) → B.ᴾᴬ γᴾᴬ
    E   : S.Tm Γ.Ec S.U
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Tm (Γ.wc γ) (B.w γc ((E ᵃt) γc))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Tm (Γ.Rc γ γᴬ) (B.R ((E ᵃt) γc) (ᴬ γᴬ))

record TmP (Γ : Con) (A : TyP Γ) : Set₂ where
  module Γ = Con Γ
  module A = TyP A
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → A.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → A.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    ᴾᴬ  : (γᴾᴬ : Γ.ᴾᴬ) → A.ᴾᴬ γᴾᴬ
    E   : ∀{γc} → _ᵃC {zero} Γ.E γc → (A.E ᵃP) γc
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc){δc : _ᵖᵃc {zero} (Γ.wc γ)} → (Γ.w γ ᵖᵃC) δc → (A.w γ (E γ) ᵖᵃP) δc
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc}(δ : _ᵖᵃC {zero} (Γ.R γ γᴬ) δc) → (A.R γ (E γ) (ᴬ γᴬ) ᵖᵃP) δc

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₂
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    ᴬ   : Γ.ᴬ → Δ.ᴬ
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → Δ.ᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    ᴾᴬ  : Γ.ᴾᴬ → Δ.ᴾᴬ
    Ec  : S.Sub Γ.Ec Δ.Ec
    E   : ∀{γc} → _ᵃC {zero} Γ.E γc → (Δ.E ᵃC) ((Ec ᵃs) γc)
    wc  : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Sub (Γ.wc γ) (Δ.wc (E γ))
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc){δc} → _ᵖᵃC {zero} (Γ.w γ) δc → (Δ.w (E γ) ᵖᵃC) ((wc γ ᵖᵃs) δc)
    Rc  : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Sub (Γ.Rc γ γᴬ) (Δ.Rc (E γ) (ᴬ γᴬ))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}{δc} → _ᵖᵃC {zero} (Γ.R γ γᴬ) δc
           → (Δ.R (E γ) (ᴬ γᴬ) ᵖᵃC) ((Rc γ γᴬ ᵖᵃs) δc)

∙ : Con
∙ = record { ᴬ  = Lift _ ⊤ ;
             ᴹ  = λ _ _ → Lift _ ⊤ ;
             ᴾᴬ = Lift _ ⊤ ;
             Ec = S.∙c ;
             E  = S.∙ ;
             wc = λ _ → S.∙c ;
             w  = λ _ → S.∙ ;
             Rc = λ _ _ → S.∙c ;
             R  = λ _ _ → S.∙ }
             
_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S B = record { ᴬ   = Σ Γ.ᴬ B.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → B.ᴹ γᴹ αᴬ βᴬ } ;
                  ᴾᴬ  = Σ Γ.ᴾᴬ B.ᴾᴬ ;
                  Ec  = Γ.Ec S.▶c S.U ;
                  E   = Γ.E S.▶S S.U ;
                  wc  = λ { {γc , α} γ → Γ.wc γ S.▶c B.w γc α } ;
                  w   = λ { {γc , α} γ → Γ.w γ S.▶S B.w γc α } ;
                  Rc  = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.Rc γ γᴬ S.▶c B.R T αᴬ } ;
                  R   = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶S B.R T αᴬ } }
  where
    module Γ = Con Γ
    module B = TyS B

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → A.ᴹ γᴹ αᴬ βᴬ } ;
                  ᴾᴬ  = Σ Γ.ᴾᴬ λ γᴾᴬ → PLift (A.ᴾᴬ γᴾᴬ) ;
                  Ec  = Γ.Ec ;
                  E   = Γ.E S.▶P A.E ;
                  wc  = λ { (γ , α) → Γ.wc γ } ;
                  w   = λ { (γ , α) → Γ.w γ S.▶P A.w γ α } ;
                  Rc  = λ { (γ , α) (γᴬ , αᴬ) → Γ.Rc γ γᴬ } ;
                  R   = λ { (γ , α) (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶P A.R γ α αᴬ } }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { ᴬ   = λ γ → Set ;
                 ᴹ   = λ γᴹ γᴬ δᴬ → γᴬ → δᴬ ;
                 ᴾᴬ  = λ γ → Prop ;
                 w   = λ γ α → α S.⇒̂S S.U ;
                 R   = λ T Tᴬ → Tᴬ S.⇒̂S (T S.⇒̂S S.U) }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { ᴬ   = λ γᴬ → a.ᴬ γᴬ ;
                    ᴹ   = λ γᴹ αᴬ βᴬ → Lift _ (a.ᴹ γᴹ αᴬ ≡ βᴬ) ;
                    ᴾᴬ  = λ γᴾᴬ → a.ᴾᴬ γᴾᴬ ;
                    E   = S.El a.E ;
                    w   = λ { γ α → S.El (a.w γ S.$S α) } ;
                    R   = λ { γ {γᴬ} α αᴬ → S.El ((a.R γ γᴬ S.$S αᴬ) S.$S α) } }
  where
    module Γ = Con Γ
    module a = TmS a

-- Internal function type
ΠS : {Γ : Con} (a : TmS Γ U) (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ)→ B.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      ᴾᴬ  = λ γᴾᴬ → (α : a.ᴾᴬ γᴾᴬ) → B.ᴾᴬ (γᴾᴬ , plift α) ;
                      w   = λ γc πᴱ → (a.E ᵃt) γc S.⇒̂S B.w γc πᴱ ;
                      R   = λ {γᴬ} πᴱ πᴬ → S.ΠS(a.ᴬ γᴬ) λ αᴬ → B.R πᴱ (πᴬ αᴬ) }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} (a : TmS Γ U) (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ) → B.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      ᴾᴬ  = λ γᴾᴬ → (α : a.ᴾᴬ γᴾᴬ) → B.ᴾᴬ (γᴾᴬ , plift α) ;
                      E   = a.E S.⇒P B.E ;
                      w   = λ {γc} γ π → S.Π^P ((a.E ᵃt) γc) λ τ → (a.w γ S.$S τ) S.⇒P B.w (γ , τ) (π τ) ;
                      R   = λ {γc} γ {γᴬ} π πᴬ → S.Π^P (a.ᴬ γᴬ)
                                                   λ αᴬ → S.Π^P ((a.E ᵃt) γc)
                                                            λ α → ((a.R γ γᴬ S.$S αᴬ) S.$S α) S.⇒P B.R (γ , α) (π α) (πᴬ αᴬ) }
  where
    module a = TmS a
    module B = TyP B
    module Γ = Con Γ

Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (f : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {Γ}{a}{B} f = record { ᴬ   = λ { (γ , α) → f.ᴬ γ α } ;
                            ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                            ᴾᴬ  = λ { (γᴾᴬ , plift α) → f.ᴾᴬ γᴾᴬ α } ;
                            E   = f.E ;
                            w   = λ { (γ , α) → f.w γ S.$S α } ;
                            R   = λ { (γ , α) (γᴬ , αᴬ) → f.R γ γᴬ S.$S αᴬ } }
  where
    module a = TmS a
    module B = TyS B
    module f = TmS f
    module Γ = Con Γ

appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (f : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
appP {a = a}{B} f = record { ᴬ   = λ { (γᴬ , αᴬ) → f.ᴬ γᴬ αᴬ } ;
                             ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                             ᴾᴬ  = λ { (γᴾᴬ , plift αᴾᴬ) → f.ᴾᴬ γᴾᴬ αᴾᴬ } ;
                             E   = λ { (γ , α) → f.E γ α } ;
                             w   = λ { (γ , α) (δ p, ω) →  f.w γ δ α ω } ;
                             R   = λ { (γ , α) (γᴬ , αᴬ) (δ p, ω) → f.R γ γᴬ δ αᴬ α ω } }
  where
    module a = TmS a
    module B = TyP B
    module f = TmP f
{-
--External function type
Π^S : {Γ : Con} (T : Set) (B : T → TyS Γ) → TyS Γ
Π^S T B = record { ᴬ   = λ γᴬ → (τ : T) → TyS.ᴬ (B τ) γᴬ ;
                  ᴹ   = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyS.ᴹ (B τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  ᴾᴬ  = λ γᴾᴬ → (τ : T) → TyS.ᴾᴬ (B τ) γᴾᴬ }

Π^P : {Γ : Con} (T : Set) (A : T → TyP Γ) → TyP Γ
Π^P T A = record { ᴬ  = λ γᴬ → (τ : T) → TyP.ᴬ (A τ) γᴬ;
                  ᴹ  = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyP.ᴹ (A τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  ᴾᴬ = λ γᴾᴬ → (τ : T) → TyP.ᴾᴬ (A τ) γᴾᴬ ;
                  E  = S.Π^P T λ τ → TyP.E (A τ) }

âppS : {Γ : Con} {T : Set} {B : T → TyS Γ} (f : TmS Γ (Π^S T B)) (τ : T) → TmS Γ (B τ)
âppS {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              ᴾᴬ = λ γᴾᴬ → f.ᴾᴬ γᴾᴬ τ ;
                              E  = f.E }
  where
    module f = TmS f
    module Γ = Con Γ

âppP : {Γ : Con} {T : Set} {B : T → TyP Γ} (f : TmP Γ (Π^P T B)) (τ : T) → TmP Γ (B τ)
âppP {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              ᴾᴬ = λ γᴾᴬ → f.ᴾᴬ γᴾᴬ τ ;
                              E  = λ γ → f.E γ τ }
  where
    module f = TmP f
-}
id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ᴬ   = λ γ → γ ;
                  ᴹ   = λ γᴹ → γᴹ ;
                  ᴾᴬ  = λ γᴾᴬ → γᴾᴬ ;
                  Ec  = S.id ;
                  E   = λ γ → γ ;
                  wc  = λ γ → S.id ;
                  w   = λ γ δ → δ ;
                  Rc  = λ γ γᴬ → S.id ;
                  R   = λ γ δ → δ }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { ᴬ   = λ γ → σ.ᴬ (δ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → σ.ᴹ (δ.ᴹ γᴹ) ;
                 ᴾᴬ  = λ γᴾᴬ → σ.ᴾᴬ (δ.ᴾᴬ γᴾᴬ) ;
                 Ec  = σ.Ec S.∘ δ.Ec ;
                 E   = λ γ → σ.E (δ.E γ) ;
                 wc  = λ γ → σ.wc (δ.E γ) S.∘ δ.wc γ ;
                 w   = λ γ δ' → σ.w (δ.E γ) (δ.w γ δ') ;
                 Rc  = λ γ γᴬ → σ.Rc (δ.E γ) (δ.ᴬ γᴬ) S.∘ δ.Rc γ γᴬ ;
                 R   = λ γ ρ → σ.R (δ.E γ) (δ.R γ ρ) }
  where
    module σ = Sub σ
    module δ = Sub δ

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { ᴬ   = λ γᴬ → B.ᴬ (σ.ᴬ γᴬ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → B.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      ᴾᴬ  = λ γᴾᴬ → B.ᴾᴬ (σ.ᴾᴬ γᴾᴬ) ;
                      w   = λ γc → B.w ((σ.Ec ᵃs) γc) ;
                      R   = λ T αᴬ → B.R T αᴬ }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { ᴬ   = λ γ → A.ᴬ (σ.ᴬ γ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → A.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      ᴾᴬ  = λ γᴾᴬ → A.ᴾᴬ (σ.ᴾᴬ γᴾᴬ) ;
                      E   = A.E S.[ σ.Ec ]T ;
                      w   = λ {γc} γ α →  A.w (σ.E γ) α S.[ σ.wc γ ]T ;
                      R   = λ {γc} γ {γᴬ} α αᴬ → A.R (σ.E γ) α αᴬ S.[ σ.Rc γ γᴬ ]T }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                ᴾᴬ  = λ γᴾᴬ → a.ᴾᴬ (σ.ᴾᴬ γᴾᴬ) ;
                                E   = a.E S.[ σ.Ec ]t ;
                                w   = λ {γc} γ → a.w (σ.E γ) S.[ σ.wc γ ]t ;
                                R   = λ {γc} γ γᴬ → a.R (σ.E γ) (σ.ᴬ γᴬ) S.[ σ.Rc γ γᴬ ]t }
  where
    module A = TyS A
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                ᴾᴬ  = λ γᴾᴬ → a.ᴾᴬ (σ.ᴾᴬ γᴾᴬ) ;
                                E   = λ {γc} γ → a.E (σ.E γ) ;
                                w   = λ γ δ → a.w (σ.E γ) (σ.w γ δ) ;
                                R   = λ {γc} γ γᴬ {δc} δ → a.R (σ.E γ) (σ.ᴬ γᴬ) {(σ.Rc γ γᴬ ᵖᵃs) δc} (σ.R γ δ) }
  where
    module A = TyP A
    module a = TmP a
    module σ = Sub σ

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} = _[_]tP
_[_]t {S} = _[_]tS

ε : ∀{Γ} → Sub Γ ∙
ε = record { ᴬ   = λ _ → lift tt ;
             ᴹ   = λ _ → lift tt ;
             Ec  = S.ε ;
             E   = λ γ → lift tt ;
             wc  = λ γ → S.ε ;
             w   = λ γ δ → ptt ;
             Rc  = λ γ γᴬ → S.ε ;
             R   = λ γ δ → ptt }

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){B : TyS Δ} → TmS Γ (B [ σ ]TS) → Sub Γ (Δ ▶S B)
σ ,tS t = record { ᴬ   = λ γᴬ → σ.ᴬ γᴬ , t.ᴬ γᴬ ;
                   ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                   ᴾᴬ  = λ γᴾᴬ → σ.ᴾᴬ γᴾᴬ , t.ᴾᴬ γᴾᴬ ;
                   Ec  = σ.Ec S., t.E ;
                   E   = λ γ → σ.E γ ;
                   wc  = λ γ → σ.wc γ S., t.w γ ;
                   w   = λ γ δ → σ.w γ δ ;
                   Rc  = λ γ γᴬ → σ.Rc γ γᴬ S., t.R γ γᴬ ;
                   R   = λ γ δ → σ.R γ δ }
  where
    module σ = Sub σ
    module t = TmS t

_,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
_,tP_ σ {A} t = record { ᴬ   = λ γᴬ → σ.ᴬ γᴬ , t.ᴬ γᴬ ;
                         ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                         ᴾᴬ  = λ γᴾᴬ → σ.ᴾᴬ γᴾᴬ , plift (t.ᴾᴬ γᴾᴬ) ;
                         Ec  = σ.Ec ;
                         E   = λ γ → σ.E γ , t.E γ ;
                         wc  = σ.wc ;
                         w   = λ γ δ → σ.w γ δ p, t.w γ δ ;
                         Rc  = λ γ γᴬ → σ.Rc γ γᴬ ;
                         R   = λ γ {γᴬ} δ → σ.R γ δ p, t.R γ γᴬ δ }
  where
    module σ = Sub σ
    module A = TyP A
    module t = TmP t

_,t_ : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,t_ {P} = _,tP_
_,t_ {S} = _,tS_

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ = record { ᴬ   = λ γᴬ → ₁ (σ.ᴬ γᴬ) ;
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 ᴾᴬ  = λ γᴾᴬ → ₁ (σ.ᴾᴬ γᴾᴬ) ;
                 Ec  = S.π₁ σ.Ec ;
                 E   = σ.E ;
                 wc  = λ γ → S.π₁ (σ.wc γ) ;
                 w   = σ.w ;
                 Rc  = λ γ γᴬ → S.π₁ (σ.Rc γ γᴬ) ;
                 R   = σ.R }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { ᴬ   = λ γᴬ → ₁ (σ.ᴬ γᴬ) ;
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 ᴾᴬ  = λ γᴾᴬ → ₁ (σ.ᴾᴬ γᴾᴬ) ; 
                 Ec  = σ.Ec ;
                 E   = λ γ → ₁ (σ.E γ) ;
                 wc  = σ.wc ;
                 w   = λ γ δ → p₁ (σ.w γ δ) ;
                 Rc  = σ.Rc ;
                 R   = λ γ δ → p₁ (σ.R γ δ) }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P}          = π₁P
π₁ {S}{Γ}{Δ}{A} = π₁S {Γ}{Δ}{A}

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S {A = A} σ ]TS)
π₂S {Γ}{Δ}{A} σ = record { ᴬ   = λ γᴬ → ₂ (σ.ᴬ γᴬ) ;
                           ᴹ   = λ γᴹ → ₂ (σ.ᴹ γᴹ) ;
                           ᴾᴬ  = λ γᴾᴬ → ₂ (σ.ᴾᴬ γᴾᴬ) ;
                           E   = S.π₂ σ.Ec ;
                           w   = λ γ → S.π₂ (σ.wc γ) ;
                           R   = λ γ γᴬ → S.π₂ (σ.Rc γ γᴬ) }
  where
    module σ = Sub σ

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P σ ]TP)
π₂P {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           ᴹ   = λ γ → ₂ (σ.ᴹ γ) ;
                           ᴾᴬ  = λ γᴾᴬ → plower (₂ (σ.ᴾᴬ γᴾᴬ)) ;
                           E   = λ {γc} γ → ₂ (σ.E γ) ;
                           w   = λ γ δ → p₂ (σ.w γ δ) ;
                           R   = λ γ γᴬ δ → p₂ (σ.R γ δ) }
  where
    module A = TyP A
    module σ = Sub σ

π₂ : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {k} σ ]T)
π₂ {P} = π₂P
π₂ {S}{Γ}{Δ}{A} = π₂S {Γ}{Δ}{A}

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

<_>S : ∀{Γ}{A : TyS Γ} → TmS Γ A → Sub Γ (Γ ▶S A)
< t >S = record
           { ᴬ = λ γᴬ → γᴬ , t.ᴬ γᴬ
           ; ᴹ = λ γᴹ → γᴹ , t.ᴹ γᴹ
           ; ᴾᴬ = λ γᴾᴬ → γᴾᴬ , t.ᴾᴬ γᴾᴬ
           ; Ec = S.id S., t.E
           ; E = λ γ → γ
           ; wc = λ γ → S.id S., t.w γ
           ; w = λ γ δ → δ
           ; Rc = λ γ γᴬ → S.id S., t.R γ γᴬ
           ; R = λ γ γᴿ → γᴿ
           }
  where
    module t = TmS t
infix 4 <_>S

<_>P : ∀{Γ}{A : TyP Γ} → TmP Γ A → Sub Γ (Γ ▶P A)
< t >P = record { ᴬ  = λ γᴬ → γᴬ , t.ᴬ γᴬ ;
                  ᴹ  = λ γᴹ → γᴹ , t.ᴹ γᴹ ;
                  ᴾᴬ = λ γᴾᴬ → γᴾᴬ , plift (t.ᴾᴬ γᴾᴬ) ;
                  Ec = S.id ;
                  E  = λ γ → γ , t.E γ ;
                  wc = λ γ → S.id ;
                  w = λ γ δ → δ p, t.w γ δ ;
                  Rc = λ γ γᴬ → S.id ;
                  R = λ γ {γᴬ} δ → δ p, t.R γ γᴬ δ }
  where
    module t = TmP t
infix 4 <_>P

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
<_> {P} = <_>P
<_> {S} = <_>S
infix 4 <_>

atS : ∀{Γ a}{B : TyS (Γ ▶P El a)}(t : TmS Γ (ΠS a B))(u : TmP Γ (El a)) → TmS Γ (B [ < u >P ]TS)
atS {Γ}{a}{B} t u = appS {Γ}{a}{B} t [ < u >P ]tS

atP : ∀{Γ a}{B : TyP (Γ ▶P El a)}(t : TmP Γ (ΠP a B))(u : TmP Γ (El a)) → TmP Γ (B [ < u >P ]TP)
atP {Γ}{a}{B} t u = appP {Γ}{a}{B} t [ < u >P ]tP

{-_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = {!!} --σ ∘ wk , ? --coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})
infixl 5 _^_-}

