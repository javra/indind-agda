{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module EWRSg where

open import Lib hiding (id; _∘_)
open import II using (PS; P; S)
--import IIA as IIA
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
    wc  : ∀{γc}(γ : _ᵃC {zero} E γc) → S.SCon
    w   : ∀{γc}(γ : (E ᵃC) γc) → S.Con (wc γ)
    Rc  : ∀{γc}(γ : _ᵃC {zero} E γc)(γᴬ : ᴬ) → S.SCon
    R   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ) → S.Con (Rc γ γᴬ)
    sg  : (γc : Ec ᵃc)(γ : (E ᵃC) γc)(δc : _ᵃc {zero} (wc γ)) → (δ : (w γ ᵃC) δc) → ᴬ

record TyS (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set₁
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → Set → S.TyS
    R   : ∀{γᴬ}(α : Set)(αᴬ : ᴬ γᴬ) → S.TyS
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc)(α : Set)(ω : _ᵃS {zero} (w γ α)) → ᴬ (Γ.sg γc γ δc δ)

record TyP (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set
    E   : S.TyP Γ.Ec
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc)(α : (E ᵃP) γc) → S.TyP (Γ.wc γ)
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}(α : (E ᵃP) γc)(αᴬ : ᴬ γᴬ) → S.TyP (Γ.Rc γ γᴬ)
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc)(α : (E ᵃP) γc)(ω : (w γ α ᵃP) δc) → ᴬ (Γ.sg γc γ δc δ)

Ty : (Γ : Con) (k : PS) → Set₂
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (A : TyS Γ) : Set₂ where
  module Γ = Con Γ
  module A = TyS A
  field
    ᴬ   : (γ : Γ.ᴬ) → A.ᴬ γ
    E   : S.Tm Γ.Ec S.U
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Tm (Γ.wc γ) (A.w γ ((E ᵃt) γc))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Tm (Γ.Rc γ γᴬ) (A.R ((E ᵃt) γc) (ᴬ γᴬ))
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc) → ᴬ (Γ.sg γc γ δc δ) ≡ A.sg γ δ ((E ᵃt) γc) ((w γ ᵃt) δc)

record TmP (Γ : Con) (A : TyP Γ) : Set₂ where
  module Γ = Con Γ
  module A = TyP A
  field
    ᴬ   : (γ : Γ.ᴬ) → A.ᴬ γ
    E   : ∀{γc} → (Γ.E ᵃC) γc → (A.E ᵃP) γc
    w   : ∀{γc}{γ : (Γ.E ᵃC) γc}{δc : Γ.wc γ ᵃc} → (Γ.w γ ᵃC) δc → (A.w γ (E γ) ᵃP) δc
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ)(δc : _ᵃc {zero} (Γ.Rc γ γᴬ)) → (δ : (Γ.R γ γᴬ ᵃC) δc) → (A.R γ (E γ) (ᴬ γᴬ) ᵃP) δc
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc) → ᴬ (Γ.sg γc γ δc δ) ≡ A.sg γ δ (E γ) (w δ)

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₂
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    ᴬ : Γ.ᴬ → Δ.ᴬ
    Ec  : S.Sub Γ.Ec Δ.Ec
    E   : ∀ γc → LSub Ec Γ.E Δ.E
    wc  : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Sub (Γ.wc γ) (Δ.wc (((E γc) ᵃsL) γ))
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc) → LSub (wc γ) (Γ.w γ) (Δ.w _)
    Rc  : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Sub (Γ.Rc γ γᴬ) (Δ.Rc ((E γc ᵃsL) γ) (ᴬ γᴬ))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}{δc}(δ : _ᵃC {zero} (Γ.R γ γᴬ) δc) → LSub {zero} (Rc γ γᴬ) (Γ.R γ γᴬ) (Δ.R ((E γc ᵃsL) γ) (ᴬ γᴬ))
    sg  : ∀{γc}(γ : _){δc}(δ : _) → ᴬ (Γ.sg γc γ δc δ) ≡ Δ.sg ((Ec ᵃs) γc) ((E γc ᵃsL) γ) ((wc γ ᵃs) δc) ((w γ δ ᵃsL) δ)

∙ : Con
∙ = record { ᴬ  = Lift _ ⊤ ;
             Ec = S.∙c ;
             E  = S.∙ ;
             wc = λ _ → S.∙c ;
             w  = λ _ → S.∙ ;
             Rc = λ _ _ → S.∙c ;
             R  = λ _ _ → S.∙ }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  Ec  = Γ.Ec S.▶c S.U ;
                  E   = Γ.E S.▶S S.U ;
                  wc  = λ { {γc , T} γ → Γ.wc γ S.▶c A.w γ T };
                  w   = λ { {γc , T} γ → Γ.w γ S.▶S A.w γ T } ;
                  Rc  = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.Rc γ γᴬ S.▶c A.R T αᴬ } ;
                  R   = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶S A.R T αᴬ } ;
                  sg  = λ { (γc , α) γ (δc , ω) δ → Γ.sg γc γ δc δ , A.sg γ δ α ω } }
  where
    module Γ = Con Γ
    module A = TyS A

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  Ec  = Γ.Ec ;
                  E   = Γ.E S.▶P A.E ;
                  wc  = λ { (γ , α) → Γ.wc γ } ;
                  w   = λ { (γ , α) → Γ.w γ S.▶P A.w γ α } ;
                  Rc  = λ { (γ , α) (γᴬ , αᴬ) → Γ.Rc γ γᴬ } ;
                  R   = λ { (γ , α) (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶P A.R γ α αᴬ } ;
                  sg  = λ { γc (γ , α) δc (δ , ω) → Γ.sg γc γ δc δ , A.sg γ δ α ω } }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { ᴬ   = λ γ → Set ;
                 w   = λ γ T → T S.⇒̂S S.U ;
                 R   = λ T Tᴬ → Tᴬ S.⇒̂S (T S.⇒̂S S.U) ;
                 sg  = λ γ δ α ω → Σ α ω }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { ᴬ   = λ γ → a.ᴬ γ ;
                    E   = S.El a.E ;
                    w   = λ { γ α → S.El (a.w γ S.$S α) } ;
                    R   = λ { γ {γᴬ} α αᴬ → S.El ((a.R γ γᴬ S.$S αᴬ) S.$S α) } ;
                    sg  = λ { γ δ α ω → coe (a.sg γ δ ⁻¹) (α , ω) } }
  where
    module Γ = Con Γ
    module a = TmS a

-- Internal function type
ΠS : {Γ : Con} (a : TmS Γ U) (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      w   = λ {γc} γ πᴱ → S.Π̂S ((a.E ᵃt) γc) λ α → B.w (γ , α) πᴱ ;
                      R   = λ {γᴬ} πᴱ πᴬ → S.Π̂S (a.ᴬ γᴬ) λ αᴬ → B.R πᴱ (πᴬ αᴬ) ;
                      sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                           coe ((λ x → B.ᴬ (_ , x)) & (coecoe⁻¹' (a.sg γ δ) α))
                                               (B.sg (γ , α₁) (δ , α₂) πc (π α₁)) }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} (a : TmS Γ U) (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                  E   = a.E S.⇒P B.E ;
                  w   = λ {γc} γ β → S.Π̂P ((a.E ᵃt) γc) λ τ → (a.w γ S.$S τ) S.⇒P B.w (γ , τ) (β τ) ;
                  R   = λ {γc} γ {γᴬ} π πᴬ → S.Π̂P (a.ᴬ γᴬ)
                                               λ αᴬ → S.Π̂P ((a.E ᵃt) γc)
                                                        λ α → ((a.R γ γᴬ S.$S αᴬ) S.$S α) S.⇒P B.R (γ , α) (π α) (πᴬ αᴬ) ;
                  sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                       coe ((λ x → B.ᴬ (_ , x)) & (coecoe⁻¹' (a.sg γ δ) α))
                                           (B.sg (γ , α₁) (δ , α₂) (πc α₁) (π α₁ α₂)) }
  where
    module a = TmS a
    module B = TyP B

Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {a = a}{B} t = record { ᴬ   = λ { (γ , α) → t.ᴬ γ α } ;
                             E   = t.E ;
                             w   = λ { (γ , α) → t.w γ S.$S α } ;
                             R   = λ { (γ , α) (γᴬ , αᴬ) → t.R γ γᴬ S.$S αᴬ } ;
                             sg  = λ { (γ , α) {δc} (δ , ω) →
                                         happly (t.sg γ δ) (coe (a.sg γ δ ⁻¹) (α , ω))
                                         ◾ apd' (λ { (α , ω) → B.sg (γ , α) (δ , ω) _ ((t.w γ ᵃt) δc α) } )
                                             (coecoe⁻¹ (a.sg γ δ) (α , ω)) } }
  where
    module a = TmS a
    module B = TyS B
    module t = TmS t

appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (t : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
appP {a = a}{B} t = record { ᴬ   = λ { (γ , α) → t.ᴬ γ α } ;
                             E   = λ { (γ , α) → t.E γ α };
                             w   = λ { {γ = γ , α} (δ , ω) → t.w δ α ω } ;
                             R   = λ { (γ , α) (γᴬ , αᴬ) δc (δ , ω) → t.R γ γᴬ δc δ αᴬ α ω } ;
                             sg  = λ { (γ , α) {δc} (δ , ω) →
                                        happly (t.sg γ δ) (coe (a.sg γ δ ⁻¹) (α , ω))
                                        ◾ apd' (λ { (α , ω) → B.sg (γ , α) (δ , ω) _ (t.w δ α ω) } )
                                            (coecoe⁻¹ (a.sg γ δ) (α , ω)) } }
  where
    module a = TmS a
    module B = TyP B
    module t = TmP t

--External function type
Π̂S : {Γ : Con} (T : Set) (B : T → TyS Γ) → TyS Γ
Π̂S T B = record { ᴬ   = λ γᴬ → (τ : T) → TyS.ᴬ (B τ) γᴬ ;
                  w   = λ γ πᴱ → S.Π̂S T λ τ → TyS.w (B τ) γ πᴱ ;
                  R   = λ πᴱ πᴬ → S.Π̂S T λ τ → TyS.R (B τ) πᴱ (πᴬ τ) ;
                  sg  = λ γ δ πᴱ πᴬ τ → TyS.sg (B τ) γ δ πᴱ (πᴬ τ) }

Π̂P : {Γ : Con} (T : Set) (B : T → TyP Γ) → TyP Γ
Π̂P T B = record { ᴬ = λ γᴬ → (τ : T) → TyP.ᴬ (B τ) γᴬ;
                  E = S.Π̂P T λ τ → TyP.E (B τ) ;
                  w = λ γ πᴱ → S.Π̂P T λ τ → TyP.w (B τ) γ (πᴱ τ) ;
                  R = λ γ πᴱ πᴬ → S.Π̂P T λ τ → TyP.R (B τ) γ (πᴱ τ) (πᴬ τ) ;
                  sg = λ γ δ πᴱ πᴬ τ → TyP.sg (B τ) γ δ (πᴱ τ) (πᴬ τ) }

âppS : {Γ : Con} {T : Set} {B : T → TyS Γ} (t : TmS Γ (Π̂S T B)) (τ : T) → TmS Γ (B τ)
âppS {Γ}{T}{B} t τ = record { ᴬ = λ γᴬ → t.ᴬ γᴬ τ ;
                              E = t.E ;
                              w = λ γ → t.w γ S.$S τ ;
                              R = λ γ γᴬ → t.R γ γᴬ S.$S τ ;
                              sg = λ γ δ → happly (t.sg γ δ) τ }
  where
    module t = TmS t

âppP : {Γ : Con} {T : Set} {B : T → TyP Γ} (t : TmP Γ (Π̂P T B)) (τ : T) → TmP Γ (B τ)
âppP {Γ}{T}{B} t τ = record { ᴬ = λ γᴬ → t.ᴬ γᴬ τ ;
                              E = λ γ → t.E γ τ ;
                              w = λ δ → t.w δ τ ;
                              R = λ γ γᴬ δc δ → t.R γ γᴬ δc δ τ ;
                              sg = λ γ δ → happly (t.sg γ δ) τ }
  where
    module t = TmP t

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ᴬ   = λ γ → γ ;
                  Ec  = S.id ;
                  E   = λ γc → Lid ;
                  wc  = λ γ → S.id ;
                  w   = λ γ δ → Lid ;
                  Rc  = λ γ γᴬ → S.id ;
                  R   = λ γ δ → Lid ;
                  sg  = λ γ δ → refl }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { ᴬ   = λ γ → σ.ᴬ (δ.ᴬ γ) ;
                 Ec  = σ.Ec S.∘ δ.Ec ;
                 E   = λ γ → σ.E ((δ.Ec ᵃs) γ) L∘ δ.E γ ;
                 wc  = λ {γc} γ → σ.wc ((δ.E γc ᵃsL) γ) S.∘ δ.wc γ ;
                 w   = λ {γc} γ {δc} δ' → σ.w ((δ.E γc ᵃsL) γ) ((δ.w γ δ' ᵃsL) δ') L∘ δ.w γ δ' ;
                 Rc  = λ {γc} γ γᴬ → σ.Rc ((δ.E γc ᵃsL) γ) (δ.ᴬ γᴬ) S.∘ δ.Rc γ γᴬ ;
                 R   = λ {γc} γ {γᴬ} δ' → σ.R ((δ.E γc ᵃsL) γ) ((δ.R γ δ' ᵃsL) δ') L∘ δ.R γ δ' ;
                 sg  = λ {γc} γ δ' → σ.ᴬ & δ.sg _ _
                                           ◾ σ.sg ((δ.E γc ᵃsL) γ) ((δ.w γ δ' ᵃsL) δ') }
  where
    module σ = Sub σ
    module δ = Sub δ

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { ᴬ   = λ γ → B.ᴬ (σ.ᴬ γ) ;
                      w   = λ {γc} γ → B.w ((σ.E γc ᵃsL) γ) ;
                      R   = λ T αᴬ → B.R T αᴬ ;
                      sg  = λ {γc} γ δ α ω → coe (B.ᴬ & (σ.sg γ δ ⁻¹))
                                                     (B.sg ((σ.E γc ᵃsL) γ) ((σ.w γ δ ᵃsL) δ) α ω) }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { ᴬ   = λ γ → A.ᴬ (σ.ᴬ γ) ;
                      E   = A.E S.[ σ.Ec ]T ;
                      w   = λ {γc} γ α →  A.w ((σ.E γc ᵃsL) γ) α S.[ σ.wc γ ]T ;
                      R   = λ {γc} γ {γᴬ} α αᴬ → A.R ((σ.E γc ᵃsL) γ) α αᴬ S.[ σ.Rc γ γᴬ ]T ;
                      sg  = λ {γc} γ δ α ω → coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                               (A.sg ((σ.E γc ᵃsL) γ) ((σ.w γ δ ᵃsL) δ) α ω) }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                E   = a.E S.[ σ.Ec ]t ;
                                w   = λ {γc} γ → a.w ((σ.E γc ᵃsL) γ) S.[ σ.wc γ ]t ;
                                R   = λ {γc} γ γᴬ → a.R ((σ.E γc ᵃsL) γ) (σ.ᴬ γᴬ) S.[ σ.Rc γ γᴬ ]t ;
                                sg  = λ {γc} γ {δc} δ →
                                              apd a.ᴬ (σ.sg γ δ ⁻¹) ⁻¹
                                              ◾ coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                                & (a.sg ((σ.E γc ᵃsL) γ) ((σ.w γ δ ᵃsL) δ)) }
  where
    module A = TyS A
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                E   = λ {γc} γ → a.E ((σ.E γc ᵃsL) γ) ;
                                w   = λ {γc}{γ}{δc} δ → a.w ((σ.w γ δ ᵃsL) δ) ;
                                R   = λ {γc} γ γᴬ δc δ → a.R ((σ.E γc ᵃsL) γ) (σ.ᴬ γᴬ) ((σ.Rc γ γᴬ ᵃs) δc) ((σ.R γ δ ᵃsL) δ) ;
                                sg  = λ {γc} γ {δc} δ → apd a.ᴬ (σ.sg γ δ ⁻¹) ⁻¹
                                                        ◾  coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                                           & a.sg ((σ.E γc ᵃsL) γ) ((σ.w γ δ ᵃsL) δ) }
  where
    module A = TyP A
    module a = TmP a
    module σ = Sub σ

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} = _[_]tP
_[_]t {S} = _[_]tS

ε : ∀{Γ} → Sub Γ ∙
ε = record { ᴬ   = λ _ → lift tt ;
             Ec  = S.ε ;
             E   = λ γ → Lε ;
             wc  = λ γ → S.ε ;
             w   = λ γ δ → Lε ;
             Rc  = λ γ γᴬ → S.ε ;
             R   = λ γ δ → Lε ;
             sg  = λ _ _ → refl }

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : TyS Δ} → TmS Γ (A [ σ ]TS) → Sub Γ (Δ ▶S A)
σ ,tS t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                   Ec  = σ.Ec S., t.E ;
                   E   = λ γ → σ.E γ ,S t.E;
                   wc  = λ γ → σ.wc γ S., t.w γ ;
                   w   = λ γ δ → σ.w γ δ ,S t.w γ ;
                   Rc  = λ γ γᴬ → σ.Rc γ γᴬ S., t.R γ γᴬ ;
                   R   = λ γ {γᴬ} δ → σ.R γ δ ,S t.R γ γᴬ ;
                   sg  = λ γ δ → ,≡ (σ.sg γ δ) (coe≡ (t.sg γ δ)) }
  where
    module σ = Sub σ
    module t = TmS t

_,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
_,tP_ σ {A} t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                         Ec  = σ.Ec ;
                         E   = λ γ → σ.E γ ,P t.E ;
                         wc  = σ.wc ;
                         w   = λ γ δ → σ.w γ δ ,P λ δ' → t.w δ' ;
                         Rc  = λ γ γᴬ → σ.Rc γ γᴬ ;
                         R   = λ γ {γᴬ} δ → σ.R γ δ ,P λ {δc'} δ' → t.R γ γᴬ δc' δ';
                         sg  = λ γ δ → ,≡ {B = A.ᴬ} (σ.sg γ δ)(coe (A.ᴬ & σ.sg γ δ) & t.sg γ δ
                                                ◾ coe∘ (A.ᴬ & σ.sg γ δ) (A.ᴬ & (σ.sg γ δ ⁻¹)) _
                                                ◾ coe-refl ) }
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
                 E   = λ γc → Lπ₁S (σ.E γc) ;
                 wc  = λ γ → S.π₁ (σ.wc γ) ;
                 w   = λ γ δ → Lπ₁S (σ.w γ δ) ;
                 Rc  = λ γ γᴬ → S.π₁ (σ.Rc γ γᴬ) ;
                 R   = λ γ δ → Lπ₁S (σ.R γ δ) ;
                 sg  = λ γ δ → ,=1 (σ.sg γ δ) }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 Ec  = σ.Ec ;
                 E   = λ γc → Lπ₁P (σ.E γc) ;
                 wc  = σ.wc ;
                 w   = λ γ δ → Lπ₁P (σ.w γ δ) ;
                 Rc  = σ.Rc ;
                 R   = λ γ δ → Lπ₁P (σ.R γ δ) ;
                 sg  = λ γ δ → ,=1 (σ.sg γ δ) }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P} = π₁P
π₁ {S} = π₁S

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           E   = S.π₂ σ.Ec ;
                           w   = λ γ → S.π₂ (σ.wc γ) ;
                           R   = λ γ γᴬ → S.π₂ (σ.Rc γ γᴬ) ;
                           sg  = λ γ δ → ,=2 {B = TyS.ᴬ A} (σ.sg γ δ ⁻¹) (₁ & σ.sg γ δ ⁻¹) ⁻¹ }
  where
    module σ = Sub σ

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P σ ]TP)
π₂P {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           E   = λ {γc} γ → ₂ ((σ.E γc ᵃsL) γ) ;
                           w   = λ {γc}{γ} δ → ₂ ((σ.w γ δ ᵃsL) δ) ;
                           R   = λ γ γᴬ δc δ → ₂ ((σ.R γ δ ᵃsL) δ) ;
                           sg  = λ γ δ → ,=2 {B = A.ᴬ} (σ.sg γ δ ⁻¹) (₁ & σ.sg γ δ ⁻¹) ⁻¹ }
  where
    module A = TyP A
    module σ = Sub σ

π₂ : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {k} σ ]T)
π₂ {P} = π₂P
π₂ {S} = π₂S

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

-- It's kind of amazing that this works
<_>S : ∀{Γ}{A : TyS Γ} → TmS Γ A → Sub Γ (Γ ▶S A)
< t >S = id ,tS t
infix 4 <_>S

<_>P : ∀{Γ}{A : TyP Γ} → TmP Γ A → Sub Γ (Γ ▶P A)
< t >P = record
           { ᴬ = λ γᴬ → γᴬ , t.ᴬ γᴬ
           ; Ec = S.id
           ; E = λ γc → Lid ,P λ γ → t.E γ
           ; wc = λ γ → S.id
           ; w = λ γ δ → Lid ,P λ δ' → t.w δ'
           ; Rc = λ γ γᴬ → S.id
           ; R = λ γ {γᴬ} δ → Lid ,P λ δ' → t.R γ γᴬ _ δ'
           ; sg = λ γ δ → ,≡ refl (t.sg γ δ)
           }
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
