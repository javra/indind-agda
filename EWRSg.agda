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
    ᴹ   : ᴬ → ᴬ → Set₁
    Ec  : S.SCon
    E   : S.Con Ec
    wc  : ∀{γc}(γ : _ᵃC {zero} E γc) → S.SCon
    w   : ∀{γc}(γ : (E ᵃC) γc) → S.Con (wc γ)
    Rc  : ∀{γc}(γ : _ᵃC {zero} E γc)(γᴬ : ᴬ) → S.SCon
    R   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ) → S.Con (Rc γ γᴬ)
    f   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ){δc : _ᵃc {zero} (wc γ)}(δ : (w γ ᵃC) δc){ρc : _ᵃc {zero} (Rc γ γᴬ)}
           (ρ : (R γ γᴬ ᵃC) ρc) → Set
    t   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ){δc : _ᵃc {zero} (wc γ)}(δ : (w γ ᵃC) δc){ρc : _ᵃc {zero} (Rc γ γᴬ)}
           (ρ : (R γ γᴬ ᵃC) ρc) → Set
    sg  : (γc : Ec ᵃc)(γ : (E ᵃC) γc)(δc : _ᵃc {zero} (wc γ)) → (δ : (w γ ᵃC) δc) → ᴬ
    m   : ∀{γc}(γ : (E ᵃC) γc)(γᴬ : ᴬ){δc : _ᵃc {zero} (wc γ)}(δ : (w γ ᵃC) δc){ρc : _ᵃc {zero} (Rc γ γᴬ)}
           (ρ : (R γ γᴬ ᵃC) ρc)(ϕ : f γ γᴬ δ ρ)(τ : t γ γᴬ δ ρ) → ᴹ (sg γc γ δc δ) γᴬ

record TyS (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set₁
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set
    w   : ∀(γc : Γ.Ec ᵃc) → Set → S.TyS
    R   : ∀{γᴬ}(α : Set)(αᴬ : ᴬ γᴬ) → S.TyS
    f   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}
           (δ : (Γ.w γ ᵃC) δc){ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)
           (α : Set)(αᴬ : ᴬ γᴬ)(αʷ : _ᵃS {zero} (w γc α))(αᴿ : _ᵃS {zero} (R α αᴬ)) → Set
    t   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}
           (δ : (Γ.w γ ᵃC) δc){ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)
           (α : Set)(αᴬ : ᴬ γᴬ)(αʷ : _ᵃS {zero} (w γc α))(αᴿ : _ᵃS {zero} (R α αᴬ)) → Set
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc)(α : Set)(ω : _ᵃS {zero} (w γc α)) → ᴬ (Γ.sg γc γ δc δ)
    m   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}(δ : (Γ.w γ ᵃC) δc)
           {ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)(ϕ : Γ.f γ γᴬ δ ρ)(τ : Γ.t γ γᴬ δ ρ)
           (α : Set)(αᴬ : ᴬ γᴬ)(αʷ : _ᵃS {zero} (w γc α))(αᴿ : _ᵃS {zero} (R α αᴬ))
           (αᶠ : f γ γᴬ δ ρ α αᴬ αʷ αᴿ)(αᵗ : t γ γᴬ δ ρ α αᴬ αʷ αᴿ)
           → ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) (sg γ δ α αʷ) αᴬ

record TyP (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set₁
    E   : S.TyP Γ.Ec
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → (E ᵃP) γc → S.TyP (Γ.wc γ)
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}(α : (E ᵃP) γc)(αᴬ : ᴬ γᴬ) → S.TyP (Γ.Rc γ γᴬ)
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc)(α : (E ᵃP) γc)(ω : (w γ α ᵃP) δc) → ᴬ (Γ.sg γc γ δc δ)
    m   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}(δ : (Γ.w γ ᵃC) δc)
           {ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)(ϕ : Γ.f γ γᴬ δ ρ)(τ : Γ.t γ γᴬ δ ρ)
           (α : (E ᵃP) γc)(αᴬ : ᴬ γᴬ)(αʷ : (w γ α ᵃP) δc)(αᴿ : (R γ α αᴬ ᵃP) ρc)
           → ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) (sg γ δ α αʷ) αᴬ

Ty : (Γ : Con) (k : PS) → Set₂
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (B : TyS Γ) : Set₂ where
  module Γ = Con Γ
  module B = TyS B
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → B.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → B.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    E   : S.Tm Γ.Ec S.U
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Tm (Γ.wc γ) (B.w γc ((E ᵃt) γc))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Tm (Γ.Rc γ γᴬ) (B.R ((E ᵃt) γc) (ᴬ γᴬ))
    f   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}(δ : (Γ.w γ ᵃC) δc)
           {ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)
           → Γ.f γ γᴬ δ ρ → B.f γ γᴬ δ ρ ((E ᵃt) γc) (ᴬ γᴬ) ((w γ ᵃt) δc) ((R γ γᴬ ᵃt) ρc)
    t   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}(δ : (Γ.w γ ᵃC) δc)
           {ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)
           → Γ.t γ γᴬ δ ρ → B.t γ γᴬ δ ρ ((E ᵃt) γc) (ᴬ γᴬ) ((w γ ᵃt) δc) ((R γ γᴬ ᵃt) ρc)
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc)
            → ᴬ (Γ.sg γc γ δc δ) ≡ B.sg γ δ ((E ᵃt) γc) ((w γ ᵃt) δc)
    m   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc : _ᵃc {zero} (Γ.wc γ)}(δ : (Γ.w γ ᵃC) δc)
           {ρc : _ᵃc {zero} (Γ.Rc γ γᴬ)}(ρ : (Γ.R γ γᴬ ᵃC) ρc)
           (ϕ : Γ.f γ γᴬ δ ρ)(τ : Γ.t γ γᴬ δ ρ)
           → coe (happly2 (B.ᴹ (B.Γ.m γ γᴬ δ ρ ϕ τ)) (sg γ δ) (ᴬ γᴬ)) (ᴹ (Γ.m γ γᴬ δ ρ ϕ τ))
             ≡ B.m γ γᴬ δ ρ ϕ τ ((E ᵃt) γc) (ᴬ γᴬ) ((w γ ᵃt) δc) ((R γ γᴬ ᵃt) ρc) (f γ γᴬ δ ρ ϕ) (t γ γᴬ δ ρ τ)

record TmP (Γ : Con) (A : TyP Γ) : Set₂ where
  module Γ = Con Γ
  module A = TyP A
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → A.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → A.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    E   : ∀{γc} → (Γ.E ᵃC) γc → (A.E ᵃP) γc
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc){δc : Γ.wc γ ᵃc} → (Γ.w γ ᵃC) δc → (A.w γ (E γ) ᵃP) δc
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ){δc}(δ : _ᵃC {zero} (Γ.R γ γᴬ) δc) → (A.R γ (E γ) (ᴬ γᴬ) ᵃP) δc
    sg  : ∀{γc}(γ : (Γ.E ᵃC) γc){δc}(δ : (Γ.w γ ᵃC) δc) → ᴬ (Γ.sg γc γ δc δ) ≡ A.sg γ δ (E γ) (w γ δ)

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₂
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    ᴬ   : Γ.ᴬ → Δ.ᴬ
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → Δ.ᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    Ec  : S.Sub Γ.Ec Δ.Ec
    E   : ∀{γc} → (Γ.E ᵃC) γc → (Δ.E ᵃC) ((Ec ᵃs) γc)
    wc  : ∀{γc}(γ : (Γ.E ᵃC) γc) → S.Sub (Γ.wc γ) (Δ.wc (E γ))
    w   : ∀{γc}(γ : (Γ.E ᵃC) γc){δc} → (Γ.w γ ᵃC) δc → (Δ.w (E γ) ᵃC) ((wc γ ᵃs) δc)
    Rc  : ∀{γc}(γ : (Γ.E ᵃC) γc)(γᴬ : Γ.ᴬ) → S.Sub (Γ.Rc γ γᴬ) (Δ.Rc (E γ) (ᴬ γᴬ))
    R   : ∀{γc}(γ : (Γ.E ᵃC) γc){γᴬ : Γ.ᴬ}{δc} → _ᵃC {zero} (Γ.R γ γᴬ) δc
           → (Δ.R (E γ) (ᴬ γᴬ) ᵃC) ((Rc γ γᴬ ᵃs) δc)
    f   : ∀{γc}(γ : _)(γᴬ : _){δc}(δ : _){ρc}(ρ : _)
           → Γ.f {γc} γ γᴬ {δc} δ {ρc} ρ → Δ.f (E γ) (ᴬ γᴬ) (w γ δ) (R γ ρ)
    t   : ∀{γc}(γ : _)(γᴬ : _){δc}(δ : _){ρc}(ρ : _)
           → Γ.t {γc} γ γᴬ {δc} δ {ρc} ρ → Δ.t (E γ) (ᴬ γᴬ) (w γ δ) (R γ ρ)
    sg  : ∀{γc}(γ : _){δc}(δ : _) → ᴬ (Γ.sg γc γ δc δ) ≡ Δ.sg ((Ec ᵃs) γc) (E γ) ((wc γ ᵃs) δc) (w γ δ)
    m   : ∀{γc}(γ : _)(γᴬ : _){δc}(δ : _){ρc} ρ ϕ τ
           → ᴹ (Γ.m {γc} γ γᴬ {δc} δ {ρc} ρ ϕ τ)
               ≡ coe (happly (Δ.ᴹ & sg γ δ) (ᴬ γᴬ) ⁻¹)
                 (Δ.m (E γ) (ᴬ γᴬ) (w γ δ) (R γ ρ) (f γ γᴬ δ ρ ϕ) (t γ γᴬ δ ρ τ))

∙ : Con
∙ = record { ᴬ  = Lift _ ⊤ ;
             ᴹ  = λ _ _ → Lift _ ⊤ ;
             Ec = S.∙c ;
             E  = S.∙ ;
             wc = λ _ → S.∙c ;
             w  = λ _ → S.∙ ;
             Rc = λ _ _ → S.∙c ;
             R  = λ _ _ → S.∙ ;
             f  = λ γ γᴬ δ ρ → Lift _ ⊤ ;
             t  = λ γ γᴬ δ ρ → Lift _ ⊤ }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S B = record { ᴬ   = Σ Γ.ᴬ B.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → B.ᴹ γᴹ αᴬ βᴬ } ;
                  Ec  = Γ.Ec S.▶c S.U ;
                  E   = Γ.E S.▶S S.U ;
                  wc  = λ { {γc , α} γ → Γ.wc γ S.▶c B.w γc α };
                  w   = λ { {γc , α} γ → Γ.w γ S.▶S B.w γc α } ;
                  Rc  = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.Rc γ γᴬ S.▶c B.R T αᴬ } ;
                  R   = λ { {γc , T} γ (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶S B.R T αᴬ } ;
                  sg  = λ { (γc , α) γ (δc , ω) δ → Γ.sg γc γ δc δ , B.sg γ δ α ω } ;
                  f   = λ { {γc , α} γ (γᴬ , αᴬ) {δc , αʷ} δ {ρc , αᴿ} ρ → Γ.f γ γᴬ δ ρ × B.f γ γᴬ δ ρ α αᴬ αʷ αᴿ } ;
                  t   = λ { {γc , α} γ (γᴬ , αᴬ) {δc , αʷ} δ {ρc , αᴿ} ρ → Γ.t γ γᴬ δ ρ × B.t γ γᴬ δ ρ α αᴬ αʷ αᴿ }  ;
                  m   = λ { {γc , α} γ (γᴬ , αᴬ) {δc , αʷ} δ {ρc , αᴿ} ρ (ϕ , αᶠ) (τ , αᵗ)
                            → Γ.m γ γᴬ δ ρ ϕ τ , B.m γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ αᶠ αᵗ } }
  where
    module Γ = Con Γ
    module B = TyS B

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → A.ᴹ γᴹ αᴬ βᴬ } ;
                  Ec  = Γ.Ec ;
                  E   = Γ.E S.▶P A.E ;
                  wc  = λ { (γ , α) → Γ.wc γ } ;
                  w   = λ { (γ , α) → Γ.w γ S.▶P A.w γ α } ;
                  Rc  = λ { (γ , α) (γᴬ , αᴬ) → Γ.Rc γ γᴬ } ;
                  R   = λ { (γ , α) (γᴬ , αᴬ) → Γ.R γ γᴬ S.▶P A.R γ α αᴬ } ;
                  f   = λ { (γ , α) (γᴬ , αᴬ) (δ , αʷ) (ρ , αᴿ) → Γ.f γ γᴬ δ ρ } ;
                  sg  = λ { γc (γ , α) δc (δ , ω) → Γ.sg γc γ δc δ , A.sg γ δ α ω } ;
                  t   = λ { (γ , α) (γᴬ , αᴬ) (δ , αʷ) (ρ , αᴿ) → Γ.t γ γᴬ δ ρ } ;
                  m   = λ { (γ , α) (γᴬ , αᴬ) (δ , αʷ) (ρ , αᴿ) ϕ τ → Γ.m γ γᴬ δ ρ ϕ τ , A.m γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ } }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { ᴬ   = λ γ → Set ;
                 ᴹ   = λ γᴹ γᴬ δᴬ → γᴬ → δᴬ ;
                 w   = λ γ α → α S.⇒̂S S.U ;
                 R   = λ T Tᴬ → Tᴬ S.⇒̂S (T S.⇒̂S S.U) ;
                 f   = λ γ γᴬ δ ρ α αᴬ αʷ αᴿ
                         → (xᴱ : α)(xᴬ₀ xᴬ₁ : αᴬ)(xʷ : αʷ xᴱ)(r₀ : αᴿ xᴬ₀ xᴱ)(r₁ : αᴿ xᴬ₁ xᴱ) → xᴬ₀ ≡ xᴬ₁ ;
                 t   = λ γ γᴬ δ ρ α αᴬ αʷ αᴿ → (xᴱ : α)(xʷ : αʷ xᴱ) → Σ αᴬ λ xᴬ → αᴿ xᴬ xᴱ ;
                 sg  = λ γ δ α ω → Σ α ω ;
                 m   = λ { γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ αᶠ αᵗ (xᴱ , xʷ) → ₁ (αᵗ xᴱ xʷ) } }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { ᴬ   = λ γᴬ → a.ᴬ γᴬ ;
                    ᴹ   = λ γᴹ αᴬ βᴬ → Lift _ (a.ᴹ γᴹ αᴬ ≡ βᴬ) ;
                    E   = S.El a.E ;
                    w   = λ { γ α → S.El (a.w γ S.$S α) } ;
                    R   = λ { γ {γᴬ} α αᴬ → S.El ((a.R γ γᴬ S.$S αᴬ) S.$S α) } ;
                    sg  = λ { γ δ α ω → coe (a.sg γ δ ⁻¹) (α , ω) } ;
                    m   = λ γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ
                            → let (αᴬ' , αᴿ') = a.t γ γᴬ δ ρ τ α αʷ in
                              let e = happly (a.m γ γᴬ δ ρ ϕ τ) (α , αʷ) in
                              let e' = a.f γ γᴬ δ ρ ϕ α αᴬ αᴬ' αʷ αᴿ αᴿ' in
                              let e'' = happly (coehapply2 (a.ᴹ (a.B.Γ.m γ γᴬ δ ρ ϕ τ)) (a.sg γ δ)) (α , αʷ) in
                              lift (e'' ⁻¹ ◾ e ◾ e' ⁻¹) }
  where
    module Γ = Con Γ
    module a = TmS a

-- Internal function type
ΠS : {Γ : Con} (a : TmS Γ U) (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ)→ B.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      w   = λ γc πᴱ → S.Π̂S ((a.E ᵃt) γc) λ α → B.w γc πᴱ ;
                      R   = λ {γᴬ} πᴱ πᴬ → S.Π̂S (a.ᴬ γᴬ) λ αᴬ → B.R πᴱ (πᴬ αᴬ) ;
                      f   = λ {γc} γ γᴬ {δc} δ {ρc} ρ π πᴬ πʷ πᴿ
                              → (xᴱ : (a.E ᵃt) γc)(xᴬ : a.ᴬ γᴬ)(xʷ : (a.w γ ᵃt) δc xᴱ)(xᴿ : (a.R γ γᴬ ᵃt) ρc xᴬ xᴱ)
                              → B.f (γ , xᴱ) (γᴬ , xᴬ) (δ , xʷ) (ρ , xᴿ) π (πᴬ xᴬ) (πʷ xᴱ) (πᴿ xᴬ) ;
                      sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                           coe ((λ x → B.ᴬ (_ , x)) & (coecoe⁻¹' (a.sg γ δ) α))
                                               (B.sg (γ , α₁) (δ , α₂) πc (π α₁)) ;
                      t   = λ {γc} γ γᴬ {δc} δ {ρc} ρ π πᴬ πʷ πᴿ
                              → (xᴱ : (a.E ᵃt) γc)(xᴬ : a.ᴬ γᴬ)(xʷ : (a.w γ ᵃt) δc xᴱ)(xᴿ : (a.R γ γᴬ ᵃt) ρc xᴬ xᴱ)
                              → B.t (γ , xᴱ) (γᴬ , xᴬ) (δ , xʷ) (ρ , xᴿ) π (πᴬ xᴬ) (πʷ xᴱ) (πᴿ xᴬ) ;
                      m   = λ {γc} γ γᴬ {δc} δ {ρc} ρ ϕ τ π πᴬ πʷ πᴿ πᶠ πᵗ αᴬ
                              → let (xᴱ , xʷ) = coe (a.sg γ δ) αᴬ in
                                let (xᴬ , xᴿ) = a.t γ γᴬ δ ρ τ xᴱ xʷ in
                                let xᴬ' = a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) αᴬ in
                                let e' = happly (a.m γ γᴬ δ ρ ϕ τ) (xᴱ , xʷ) in
                                let xᴿ' = coe (happly2 ((a.R γ γᴬ ᵃt) ρc) e' xᴱ ⁻¹) xᴿ in
                                let e'' = happly (coehapply2 (a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ)) (a.sg γ δ)) (xᴱ , xʷ)
                                          ◾ a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) & coecoe⁻¹' (a.sg γ δ) αᴬ in
                                let e = a.f γ γᴬ δ ρ ϕ xᴱ xᴬ xᴬ' xʷ xᴿ (coe (happly2 ((a.R γ γᴬ ᵃt) ρc) e'' xᴱ) xᴿ') in
                                coe
                                (Bᴹaux _ _ _ _ _ _ (coecoe⁻¹' (a.sg γ δ) αᴬ) e (Lift-irrel _ _) _
                                  (B.ᴬ & ,≡ refl e) (coe-coe _ _ (πᴬ xᴬ) ◾ apd πᴬ e))
                                (B.m {γc} (γ , xᴱ) (γᴬ , xᴬ) (δ , xʷ) {ρc} (ρ , xᴿ) ϕ τ
                                     π (πᴬ xᴬ) (πʷ xᴱ) (πᴿ xᴬ) (πᶠ xᴱ xᴬ xʷ xᴿ) (πᵗ xᴱ xᴬ xʷ xᴿ)) }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B
    Bᴹaux : ∀ {γᴬ₀ γᴬ₁ αᴬ₀ αᴬ₀' αᴬ₁ αᴬ₁'} (γᴹ : Γ.ᴹ γᴬ₀ γᴬ₁) (αᴹ : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀ ≡ αᴬ₁)) (αᴹ' : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀' ≡ αᴬ₁'))
              (βᴬ₀ : B.ᴬ (γᴬ₀ , αᴬ₀)) (βᴬ₁ : B.ᴬ (γᴬ₁ , αᴬ₁)) (βᴬ₁' : B.ᴬ (γᴬ₁ , αᴬ₁'))
              (αᴬ₀≡ : αᴬ₀ ≡ αᴬ₀') (αᴬ₁≡ : αᴬ₁ ≡ αᴬ₁') (αᴹ≡ : coe (Lift _ & ≡≡ (a.ᴹ γᴹ & αᴬ₀≡) αᴬ₁≡) αᴹ ≡ αᴹ')
              (Bᴬ₀≡ : B.ᴬ (γᴬ₀ , αᴬ₀) ≡ B.ᴬ (γᴬ₀ , αᴬ₀')) (Bᴬ₁≡ : B.ᴬ (γᴬ₁ , αᴬ₁) ≡ B.ᴬ (γᴬ₁ , αᴬ₁')) (βᴬ₁≡ : coe Bᴬ₁≡ βᴬ₁ ≡ βᴬ₁')
              → B.ᴹ (γᴹ , αᴹ) βᴬ₀ βᴬ₁ ≡ B.ᴹ (γᴹ , αᴹ') (coe Bᴬ₀≡ βᴬ₀) βᴬ₁'
    Bᴹaux γᴹ αᴹ .αᴹ βᴬ₀ βᴬ₁ .βᴬ₁ refl refl refl refl refl refl = refl

ΠP : {Γ : Con} (a : TmS Γ U) (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ) → B.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      E   = a.E S.⇒P B.E ;
                      w   = λ {γc} γ π → S.Π̂P ((a.E ᵃt) γc) λ τ → (a.w γ S.$S τ) S.⇒P B.w (γ , τ) (π τ) ;
                      R   = λ {γc} γ {γᴬ} π πᴬ → S.Π̂P (a.ᴬ γᴬ)
                                                   λ αᴬ → S.Π̂P ((a.E ᵃt) γc)
                                                            λ α → ((a.R γ γᴬ S.$S αᴬ) S.$S α) S.⇒P B.R (γ , α) (π α) (πᴬ αᴬ) ;
                      sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                           coe ((λ x → B.ᴬ (_ , x)) & (coecoe⁻¹' (a.sg γ δ) α))
                                               (B.sg (γ , α₁) (δ , α₂) (πc α₁) (π α₁ α₂)) ;
                      m   = λ γ γᴬ δ {ρc} ρ ϕ τ π πᴬ πʷ πᴿ αᴬ
                              → let (xᴱ , xʷ) = coe (a.sg γ δ) αᴬ in
                                let (xᴬ , xᴿ) = a.t γ γᴬ δ ρ τ xᴱ xʷ in
                                let xᴬ' = a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) αᴬ in
                                let xᴿ' = coe (happly2 ((a.R γ γᴬ ᵃt) ρc) (happly (a.m γ γᴬ δ ρ ϕ τ) (xᴱ , xʷ)) xᴱ ⁻¹) xᴿ in
                                let e'' = happly (coehapply2 (a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ)) (a.sg γ δ)) (xᴱ , xʷ)
                                          ◾ a.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ) & coecoe⁻¹' (a.sg γ δ) αᴬ in
                                let e = a.f γ γᴬ δ ρ ϕ xᴱ xᴬ xᴬ' xʷ xᴿ (coe (happly2 ((a.R γ γᴬ ᵃt) ρc) e'' xᴱ) xᴿ') in
                                coe (Bᴹaux _ _ _ _ _ _ (coecoe⁻¹' (a.sg γ δ) αᴬ) e
                                  (Lift-irrel _ _) _ (B.ᴬ & ,≡ refl e) (coe-coe _ _ (πᴬ xᴬ) ◾ apd πᴬ e))
                                  (B.m (γ , xᴱ) (γᴬ , xᴬ) (δ , xʷ) (ρ , xᴿ) ϕ τ (π xᴱ) (πᴬ xᴬ) (πʷ xᴱ xʷ) (πᴿ xᴬ xᴱ xᴿ)) }
  where
    module a = TmS a
    module B = TyP B
    module Γ = Con Γ
    Bᴹaux : ∀ {γᴬ₀ γᴬ₁ αᴬ₀ αᴬ₀' αᴬ₁ αᴬ₁'} (γᴹ : Γ.ᴹ γᴬ₀ γᴬ₁)
              (αᴹ : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀ ≡ αᴬ₁)) (αᴹ' : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀' ≡ αᴬ₁'))
              (βᴬ₀ : B.ᴬ (γᴬ₀ , αᴬ₀)) (βᴬ₁ : B.ᴬ (γᴬ₁ , αᴬ₁)) (βᴬ₁' : B.ᴬ (γᴬ₁ , αᴬ₁'))
              (αᴬ₀≡ : αᴬ₀ ≡ αᴬ₀') (αᴬ₁≡ : αᴬ₁ ≡ αᴬ₁') (αᴹ≡ : coe (Lift _ & ≡≡ (a.ᴹ γᴹ & αᴬ₀≡) αᴬ₁≡) αᴹ ≡ αᴹ')
              (Bᴬ₀≡ : B.ᴬ (γᴬ₀ , αᴬ₀) ≡ B.ᴬ (γᴬ₀ , αᴬ₀')) (Bᴬ₁≡ : B.ᴬ (γᴬ₁ , αᴬ₁) ≡ B.ᴬ (γᴬ₁ , αᴬ₁')) (βᴬ₁≡ : coe Bᴬ₁≡ βᴬ₁ ≡ βᴬ₁')
              → B.ᴹ (γᴹ , αᴹ) βᴬ₀ βᴬ₁ ≡ B.ᴹ (γᴹ , αᴹ') (coe Bᴬ₀≡ βᴬ₀) βᴬ₁'
    Bᴹaux γᴹ αᴹ .αᴹ βᴬ₀ βᴬ₁ .βᴬ₁ refl refl refl refl refl refl = refl


Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

{-
appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (f : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {Γ}{a}{B} f = record { ᴬ   = λ { (γ , α) → f.ᴬ γ α } ;
                            ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                            E   = f.E ;
                            w   = λ { (γ , α) → f.w γ S.$S α } ;
                            R   = λ { (γ , α) (γᴬ , αᴬ) → f.R γ γᴬ S.$S αᴬ } ;
                            sg  = λ { (γ , α) {δc} (δ , ω) →
                                        happly (f.sg γ δ) (coe (a.sg γ δ ⁻¹) (α , ω))
                                        ◾ apd' (λ { (α , ω) → B.sg (γ , α) (δ , ω) _ ((f.w γ ᵃt) δc α) } )
                                            (coecoe⁻¹ (a.sg γ δ) (α , ω)) } ;
                            f   = λ { (γ , α) (γᴬ , αᴬ) (δ , αʷ) (ρ , αᴿ) ϕ → f.f γ γᴬ δ ρ ϕ α αᴬ αʷ αᴿ } ;
                            t   = λ { (γ , α) (γᴬ , αᴬ) (δ , αʷ) (ρ , αᴿ) τ → f.t γ γᴬ δ ρ τ α αᴬ αʷ αᴿ } ;
                            m   = λ { {γc} (γ , α) (γᴬ , αᴬ) {δc} (δ , αʷ) {ρc} (ρ , αᴿ) ϕ τ
                                      → let e = happly (f.m γ γᴬ δ ρ ϕ τ) (coe (a.sg γ δ ⁻¹) (α , αʷ)) in
                                        --let ae = a.m γ γᴬ δ ρ ϕ τ in
                                        coe-coe {!!} {!!} {!!}
                                        ◾ coe≡ e
                                        ◾ Bᵐcoecoe γ γᴬ δ ρ ϕ τ (coe (a.sg γ δ) (coe (a.sg γ δ ⁻¹) (α , αʷ)))
                                            (α , αʷ) (αᴬ , αᴿ) (a.sg γ δ)
                                            {!!} } }
                                        -- essentially e
  where
    module a = TmS a
    module B = TyS B
    module f = TmS f
    module Γ = Con Γ
    Bᴹaux : ∀ {γᴬ₀ γᴬ₁ αᴬ₀ αᴬ₀' αᴬ₁ αᴬ₁'} (γᴹ : Γ.ᴹ γᴬ₀ γᴬ₁) (αᴹ : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀ ≡ αᴬ₁)) (αᴹ' : Lift (suc zero) (a.ᴹ γᴹ αᴬ₀' ≡ αᴬ₁'))
              (βᴬ₀ : B.ᴬ (γᴬ₀ , αᴬ₀)) (βᴬ₁ : B.ᴬ (γᴬ₁ , αᴬ₁)) (βᴬ₁' : B.ᴬ (γᴬ₁ , αᴬ₁'))
              (αᴬ₀≡ : αᴬ₀ ≡ αᴬ₀') (αᴬ₁≡ : αᴬ₁ ≡ αᴬ₁') (αᴹ≡ : coe (Lift _ & ≡≡ (a.ᴹ γᴹ & αᴬ₀≡) αᴬ₁≡) αᴹ ≡ αᴹ')
              (Bᴬ₀≡ : B.ᴬ (γᴬ₀ , αᴬ₀) ≡ B.ᴬ (γᴬ₀ , αᴬ₀')) (Bᴬ₁≡ : B.ᴬ (γᴬ₁ , αᴬ₁) ≡ B.ᴬ (γᴬ₁ , αᴬ₁')) (βᴬ₁≡ : coe Bᴬ₁≡ βᴬ₁ ≡ βᴬ₁')
              → B.ᴹ (γᴹ , αᴹ) βᴬ₀ βᴬ₁ ≡ B.ᴹ (γᴹ , αᴹ') (coe Bᴬ₀≡ βᴬ₀) βᴬ₁'
    Bᴹaux γᴹ αᴹ .αᴹ βᴬ₀ βᴬ₁ .βᴬ₁ refl refl refl refl refl refl = refl
    Bᵐcoecoe : ∀ {γc} γ γᴬ {δc} δ {ρc} ρ ϕ τ ααʷ ααʷ'
                 αᴬᴿ'
                 (p : a.ᴬ (Γ.sg γc γ δc δ) ≡ Σ ((a.E ᵃt) γc) ((a.w γ ᵃt) δc)) q →
                   let (pp₁ , pp₂) = (coe p (coe (p ⁻¹) ααʷ)) in
                   let (t₁ , t₂)  = (a.t γ γᴬ δ ρ τ pp₁ pp₂) in
                   coe q (B.m (γ , pp₁) (γᴬ , t₁) (δ , pp₂) (ρ , t₂) ϕ τ ((f.E ᵃt) γc)
                     (f.ᴬ γᴬ t₁) ((f.w γ ᵃt) δc pp₁) ((f.R γ γᴬ ᵃt) ρc t₁) 
                     (f.f γ γᴬ δ ρ ϕ pp₁ t₁ pp₂ t₂) (f.t γ γᴬ δ ρ τ pp₁ t₁ pp₂ t₂))
                   ≡ B.m (γ , ₁ ααʷ') (γᴬ , ₁ αᴬᴿ') (δ , ₂ ααʷ') (ρ , ₂ αᴬᴿ') ϕ τ
                     ((f.E ᵃt) γc) (f.ᴬ γᴬ (₁ αᴬᴿ')) ((f.w γ ᵃt) δc (₁ ααʷ')) ((f.R γ γᴬ ᵃt) ρc (₁ αᴬᴿ'))
                     (f.f γ γᴬ δ ρ ϕ (₁ ααʷ') (₁ αᴬᴿ') (₂ ααʷ') (₂ αᴬᴿ'))
                     (f.t γ γᴬ δ ρ τ (₁ ααʷ') (₁ αᴬᴿ') (₂ ααʷ') (₂ αᴬᴿ'))
    Bᵐcoecoe γ γᴬ δ ρ ϕ τ ααʷ ααʷ' p q = {!!}
-}

appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (f : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
appP {a = a}{B} f = record { ᴬ   = λ { (γ , α) → f.ᴬ γ α } ;
                             ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                             E   = λ { (γ , α) → f.E γ α };
                             w   = λ { (γ , α) (δ , ω) → f.w γ δ α ω } ;
                             R   = λ { (γ , α) (γᴬ , αᴬ) (δ , ω) → f.R γ γᴬ δ αᴬ α ω } ;
                             sg  = λ { (γ , α) {δc} (δ , ω) →
                                        happly (f.sg γ δ) (coe (a.sg γ δ ⁻¹) (α , ω))
                                        ◾ apd' (λ { (α , ω) → B.sg (γ , α) (δ , ω) _ (f.w γ δ α ω) } )
                                            (coecoe⁻¹ (a.sg γ δ) (α , ω)) } }
  where
    module a = TmS a
    module B = TyP B
    module f = TmP f

--External function type
Π̂S : {Γ : Con} (T : Set) (B : T → TyS Γ) → TyS Γ
Π̂S T B = record { ᴬ   = λ γᴬ → (τ : T) → TyS.ᴬ (B τ) γᴬ ;
                  ᴹ   = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyS.ᴹ (B τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  w   = λ γ πᴱ → S.Π̂S T λ τ → TyS.w (B τ) γ πᴱ ;
                  R   = λ πᴱ πᴬ → S.Π̂S T λ τ → TyS.R (B τ) πᴱ (πᴬ τ) ;
                  f   = λ γ γᴬ δ ρ π πᴬ πʷ πᴿ → (τ : T) → TyS.f (B τ) γ γᴬ δ ρ π (πᴬ τ) (πʷ τ) (πᴿ τ) ;
                  t   = λ γ γᴬ δ ρ π πᴬ πʷ πᴿ → (τ : T) → TyS.t (B τ) γ γᴬ δ ρ π (πᴬ τ) (πʷ τ) (πᴿ τ) ;
                  sg  = λ γ δ πᴱ πᴬ τ → TyS.sg (B τ) γ δ πᴱ (πᴬ τ) ;
                  m   = λ γ γᴬ δ ρ ϕ τ' π πᴬ πʷ πᴿ πᶠ πᵗ τ
                          → TyS.m (B τ) γ γᴬ δ ρ ϕ τ' π (πᴬ τ) (πʷ τ) (πᴿ τ) (πᶠ τ) (πᵗ τ) }

Π̂P : {Γ : Con} (T : Set) (A : T → TyP Γ) → TyP Γ
Π̂P T A = record { ᴬ  = λ γᴬ → (τ : T) → TyP.ᴬ (A τ) γᴬ;
                  ᴹ  = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyP.ᴹ (A τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  E  = S.Π̂P T λ τ → TyP.E (A τ) ;
                  w  = λ γ πᴱ → S.Π̂P T λ τ → TyP.w (A τ) γ (πᴱ τ) ;
                  R  = λ γ πᴱ πᴬ → S.Π̂P T λ τ → TyP.R (A τ) γ (πᴱ τ) (πᴬ τ) ;
                  sg = λ γ δ πᴱ πᴬ τ → TyP.sg (A τ) γ δ (πᴱ τ) (πᴬ τ) ;
                  m  = λ γ γᴬ δ ρ ϕ τ' π πᴬ πʷ πᴿ τ
                         → TyP.m (A τ) γ γᴬ δ ρ ϕ τ' (π τ) (πᴬ τ) (πʷ τ) (πᴿ τ) }

âppS : {Γ : Con} {T : Set} {B : T → TyS Γ} (f : TmS Γ (Π̂S T B)) (τ : T) → TmS Γ (B τ)
âppS {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              E  = f.E ;
                              w  = λ γ → f.w γ S.$S τ ;
                              R  = λ γ γᴬ → f.R γ γᴬ S.$S τ ;
                              f  = λ γ γᴬ δ ρ ϕ → f.f γ γᴬ δ ρ ϕ τ ;
                              t  = λ γ γᴬ δ ρ τ' → f.t γ γᴬ δ ρ τ' τ ;
                              sg = λ γ δ → happly (f.sg γ δ) τ ;
                              m  = λ γ γᴬ δ ρ ϕ τ'
                                     → coe→ (f.ᴹ (Γ.m γ γᴬ δ ρ ϕ τ')) τ _ _
                                       (ext (λ τ → happly2 (TyS.ᴹ (B τ) (f.B.Γ.m γ γᴬ δ ρ ϕ τ'))
                                                   (happly (f.sg γ δ) τ) (f.ᴬ γᴬ τ))) ⁻¹
                                       ◾ happly (f.m γ γᴬ δ ρ ϕ τ') τ }
  where
    module f = TmS f
    module Γ = Con Γ

âppP : {Γ : Con} {T : Set} {B : T → TyP Γ} (f : TmP Γ (Π̂P T B)) (τ : T) → TmP Γ (B τ)
âppP {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              E  = λ γ → f.E γ τ ;
                              w  = λ γ δ → f.w γ δ τ ;
                              R  = λ γ γᴬ δ → f.R γ γᴬ δ τ ;
                              sg = λ γ δ → happly (f.sg γ δ) τ }
  where
    module f = TmP f

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ᴬ   = λ γ → γ ;
                  ᴹ   = λ γᴹ → γᴹ ;
                  Ec  = S.id ;
                  E   = λ γ → γ ;
                  wc  = λ γ → S.id ;
                  w   = λ γ δ → δ ;
                  Rc  = λ γ γᴬ → S.id ;
                  R   = λ γ δ → δ ;
                  f   = λ γ γᴬ δ ρ x → x ;
                  t   = λ γ γᴬ δ ρ x → x ;
                  sg  = λ γ δ → refl ;
                  m   = λ γ γᴬ δ ρ ϕ τ → refl }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { ᴬ   = λ γ → σ.ᴬ (δ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → σ.ᴹ (δ.ᴹ γᴹ) ;
                 Ec  = σ.Ec S.∘ δ.Ec ;
                 E   = λ γ → σ.E (δ.E γ) ;
                 wc  = λ γ → σ.wc (δ.E γ) S.∘ δ.wc γ ;
                 w   = λ γ δ' → σ.w (δ.E γ) (δ.w γ δ') ;
                 Rc  = λ γ γᴬ → σ.Rc (δ.E γ) (δ.ᴬ γᴬ) S.∘ δ.Rc γ γᴬ ;
                 R   = λ γ ρ → σ.R (δ.E γ) (δ.R γ ρ) ;
                 f   = λ γ γᴬ δ' ρ x → σ.f (δ.E γ) (δ.ᴬ γᴬ) (δ.w γ δ') (δ.R γ ρ) (δ.f γ γᴬ δ' ρ x) ;
                 t   = λ γ γᴬ δ' ρ x → σ.t (δ.E γ) (δ.ᴬ γᴬ) (δ.w γ δ') (δ.R γ ρ) (δ.t γ γᴬ δ' ρ x) ;
                 sg  = λ γ δ' → σ.ᴬ & δ.sg _ _ ◾ σ.sg (δ.E γ) (δ.w γ δ') ;
                 m   = λ γ γᴬ δ' ρ ϕ τ
                       → let σm = σ.m (δ.E γ) (δ.ᴬ γᴬ) (δ.w γ δ') (δ.R γ ρ) (δ.f γ γᴬ δ' ρ ϕ)
                                    (δ.t γ γᴬ δ' ρ τ) in
                         let σm' = coe≡ {p = happly (σ.Δ.ᴹ & σ.sg (δ.E γ) (δ.w γ δ')) (σ.ᴬ (δ.ᴬ γᴬ))}
                                     {q = happly (σ.Δ.ᴹ & σ.sg (δ.E γ) (δ.w γ δ')) (σ.ᴬ (δ.ᴬ γᴬ)) ⁻¹} σm in
                         let δm = δ.m γ γᴬ δ' ρ ϕ τ in
                         σ.ᴹ & δm
                         ◾ {!!} -- just path algebra
                         ◾ coe (happly (σ.Δ.ᴹ & (σ.ᴬ & δ.sg γ δ' ◾ σ.sg (δ.E γ) (δ.w γ δ')))
                               (σ.ᴬ (δ.ᴬ γᴬ)) ⁻¹) & σm'}
  where
    module σ = Sub σ
    module δ = Sub δ
{-
_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { ᴬ   = λ γ → B.ᴬ (σ.ᴬ γ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → B.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      w   = λ γc → B.w ((σ.Ec ᵃs) γc) ;
                      R   = λ T αᴬ → B.R T αᴬ ;
                      f   = λ γ γᴬ δ ρ α αᴬ αʷ αᴿ → B.f (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) α αᴬ αʷ αᴿ ;
                      sg  = λ {γc} γ δ α ω → coe (B.ᴬ & (σ.sg γ δ ⁻¹))
                                                     (B.sg (σ.E γ) (σ.w γ δ) α ω) ;
                      t   = λ γ γᴬ δ ρ α αᴬ αʷ αᴿ → B.t (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) α αᴬ αʷ αᴿ ;
                      m   = λ γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ αᶠ αᵗ → coe {!!}
                                                                (B.m (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) (σ.f γ γᴬ δ ρ ϕ)
                                                                 (σ.t γ γᴬ δ ρ τ) α αᴬ αʷ αᴿ αᶠ αᵗ) }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { ᴬ   = λ γ → A.ᴬ (σ.ᴬ γ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → A.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      E   = A.E S.[ σ.Ec ]T ;
                      w   = λ {γc} γ α →  A.w (σ.E γ) α S.[ σ.wc γ ]T ;
                      R   = λ {γc} γ {γᴬ} α αᴬ → A.R (σ.E γ) α αᴬ S.[ σ.Rc γ γᴬ ]T ;
                      sg  = λ {γc} γ δ α ω → coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                               (A.sg (σ.E γ) (σ.w γ δ) α ω) ;
                      m   = λ γ γᴬ δ ρ ϕ τ α αᴬ αʷ αᴿ → {!!} }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                E   = a.E S.[ σ.Ec ]t ;
                                w   = λ {γc} γ → a.w (σ.E γ) S.[ σ.wc γ ]t ;
                                R   = λ {γc} γ γᴬ → a.R (σ.E γ) (σ.ᴬ γᴬ) S.[ σ.Rc γ γᴬ ]t ;
                                f   = λ γ γᴬ δ ρ ϕ → a.f (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) (σ.f γ γᴬ δ ρ ϕ) ;
                                t   = λ γ γᴬ δ ρ τ → a.t (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) (σ.t γ γᴬ δ ρ τ) ;
                                sg  = λ {γc} γ {δc} δ →
                                              apd a.ᴬ (σ.sg γ δ ⁻¹) ⁻¹
                                              ◾ coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                                & (a.sg (σ.E γ) (σ.w γ δ)) ;
                                m   = λ γ γᴬ δ ρ ϕ τ
                                        → let m' = a.m (σ.E γ) (σ.ᴬ γᴬ) (σ.w γ δ) (σ.R γ ρ) (σ.f γ γᴬ δ ρ ϕ) (σ.t γ γᴬ δ ρ τ) in
                                          {!!} }
  where
    module A = TyS A
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                E   = λ {γc} γ → a.E (σ.E γ) ;
                                w   = λ γ δ → a.w (σ.E γ) (σ.w γ δ) ;
                                R   = λ {γc} γ γᴬ {δc} δ → a.R (σ.E γ) (σ.ᴬ γᴬ) {(σ.Rc γ γᴬ ᵃs) δc} (σ.R γ δ) ;
                                sg  = λ {γc} γ {δc} δ → apd a.ᴬ (σ.sg γ δ ⁻¹) ⁻¹
                                                        ◾  coe (A.ᴬ & (σ.sg γ δ ⁻¹))
                                                           & a.sg (σ.E γ) (σ.w γ δ) }
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
             w   = λ γ δ → lift tt ;
             Rc  = λ γ γᴬ → S.ε ;
             R   = λ γ δ → lift tt ;
             sg  = λ _ _ → refl }

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){B : TyS Δ} → TmS Γ (B [ σ ]TS) → Sub Γ (Δ ▶S B)
σ ,tS t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                   ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                   Ec  = σ.Ec S., t.E ;
                   E   = λ γ → σ.E γ;
                   wc  = λ γ → σ.wc γ S., t.w γ ;
                   w   = λ γ δ → σ.w γ δ ;
                   Rc  = λ γ γᴬ → σ.Rc γ γᴬ S., t.R γ γᴬ ;
                   R   = λ γ δ → σ.R γ δ ;
                   f   = λ γ γᴬ δ ρ x → σ.f γ γᴬ δ ρ x , t.f γ γᴬ δ ρ x ;
                   t   = λ γ γᴬ δ ρ x → σ.t γ γᴬ δ ρ x , t.t γ γᴬ δ ρ x ;
                   sg  = λ γ δ → ,≡ (σ.sg γ δ) (coe≡ (t.sg γ δ)) }
  where
    module σ = Sub σ
    module t = TmS t

_,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
_,tP_ σ {A} t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                         ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                         Ec  = σ.Ec ;
                         E   = λ γ → σ.E γ , t.E γ ;
                         wc  = σ.wc ;
                         w   = λ γ δ → σ.w γ δ , t.w γ δ ;
                         Rc  = λ γ γᴬ → σ.Rc γ γᴬ ;
                         R   = λ γ {γᴬ} δ → σ.R γ δ , t.R γ γᴬ δ;
                         f   = λ γ γᴬ δ ρ x → σ.f γ γᴬ δ ρ x ;
                         t   = λ γ γᴬ δ ρ x → σ.t γ γᴬ δ ρ x ;
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
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 Ec  = S.π₁ σ.Ec ;
                 E   = σ.E ;
                 wc  = λ γ → S.π₁ (σ.wc γ) ;
                 w   = σ.w ;
                 Rc  = λ γ γᴬ → S.π₁ (σ.Rc γ γᴬ) ;
                 R   = σ.R ;
                 f   = λ γ γᴬ δ ρ x → ₁ (σ.f γ γᴬ δ ρ x) ;
                 t   = λ γ γᴬ δ ρ x → ₁ (σ.t γ γᴬ δ ρ x) ;
                 sg  = λ γ δ → ,=1 (σ.sg γ δ) }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 Ec  = σ.Ec ;
                 E   = λ γ → ₁ (σ.E γ) ;
                 wc  = σ.wc ;
                 w   = λ γ δ → ₁ (σ.w γ δ) ;
                 Rc  = σ.Rc ;
                 R   = λ γ δ → ₁ (σ.R γ δ) ;
                 f   = σ.f ;
                 t   = σ.t ;
                 sg  = λ γ δ → ,=1 (σ.sg γ δ) }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P} = π₁P
π₁ {S} = π₁S
{-
π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           ᴹ   = λ γᴹ → ₂ (σ.ᴹ γᴹ) ;
                           E   = S.π₂ σ.Ec ;
                           w   = λ γ → S.π₂ (σ.wc γ) ;
                           R   = λ γ γᴬ → S.π₂ (σ.Rc γ γᴬ) ;
                           f   = λ γ γᴬ δ ρ ϕ → ₂ (σ.f γ γᴬ δ ρ ϕ) ;
                           t   = λ γ γᴬ δ ρ τ → ₂ (σ.t γ γᴬ δ ρ τ) ;
                           sg  = λ γ δ → ,=2 {B = TyS.ᴬ A} (σ.sg γ δ ⁻¹) (₁ & σ.sg γ δ ⁻¹) ⁻¹ ;
                           m   = λ γ γᴬ δ ρ ϕ τ → {!!} }
  where
    module σ = Sub σ

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P σ ]TP)
π₂P {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           ᴹ   = λ γ → ₂ (σ.ᴹ γ) ;
                           E   = λ {γc} γ → ₂ (σ.E γ) ;
                           w   = λ γ δ → ₂ (σ.w γ δ) ;
                           R   = λ γ γᴬ δ → ₂ (σ.R γ δ) ;
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
           { ᴬ = λ γᴬ → γᴬ , t.ᴬ γᴬ ;
             ᴹ = λ γᴹ → γᴹ , t.ᴹ γᴹ ;
             Ec = S.id ;
             E = λ γ → γ , t.E γ ;
             wc = λ γ → S.id ;
             w = λ γ δ → δ , t.w γ δ ;
             Rc = λ γ γᴬ → S.id ;
             R = λ γ {γᴬ} δ → δ , t.R γ γᴬ δ ;
             sg = λ γ δ → ,≡ refl (t.sg γ δ) }
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
-}
-}
