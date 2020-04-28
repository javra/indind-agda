{-# OPTIONS --rewriting --allow-unsolved-metas #-}
open import Lib hiding (id; _∘_)
open import IFA
open import IFD
import E

module W (Ω : E.Con)
  {ωc : _ᵃc {zero} (E.Con.Ec Ω)}(ω : (E.Con.E Ω ᵃC) ωc) where

  module Ω = E.Con Ω

{-
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
infixl 3 _▶P_
-}
  infixl 3 _▶S_

  record Con : Set₃ where
    field
      E  : E.Con
      wc : (σ : E.Sub Ω E) → ᵈc {suc zero} (E.Con.Ec E) ((E.Sub.Ec σ ᵃs) ωc)

  record TyS (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      E : E.TyS Γ.E
      w : _ᵃc {zero} (E.Con.Ec Γ.E) → Set₁

  record TyP (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      E : E.TyP Γ.E

  record TmS (Γ : Con) (B : TyS Γ) : Set₃ where
    module Γ = Con Γ
    module B = TyS B
    field
      E  : E.TmS Γ.E B.E
      w' : Set₁
      w  : ∀(σ : E.Sub Ω Γ.E) α → ᵈt (E.TmS.E E) (Γ.wc σ) α ≡ w'

  record TmP (Γ : Con) (A : TyP Γ) : Set₃ where
    module Γ = Con Γ
    module A = TyP A
    field
      E : E.TmP Γ.E A.E

  ∙ : Con
  ∙ = record { E = E.∙
             }

  _▶S_ : (Γ : Con) → TyS Γ → Con
  Γ ▶S B = record { E  = Γ.E E.▶S B.E
                  ; wc = λ σ → Γ.wc (E.π₁S σ) , λ _ → B.w ((E.Sub.Ec (E.π₁S σ) ᵃs) ωc)
                  }
    where
      module Γ = Con Γ
      module B = TyS B

  _▶P_ : (Γ : Con) → TyP Γ → Con
  Γ ▶P A = record { E  = Γ.E E.▶P A.E
                  ; wc = λ σ → Γ.wc (E.π₁P σ)
                  }
    where
      module Γ = Con Γ
      module A = TyP A

  U : {Γ : Con} → TyS Γ
  U {Γ} = record { E = E.U
                 ; w = λ _ → Set
                 }
    where
      module Γ = Con Γ

  El : {Γ : Con} (a : TmS Γ U) → TyP Γ
  El {Γ} a = record { E = E.El a.E
                    }
    where
      module Γ = Con Γ
      module a = TmS a

  ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
  ΠS {Γ} a B = record { E = E.ΠS a.E B.E
                      ; w = λ γ → (aS.E ᵃt) γ → B.w γ
                      }
    where
      module Γ = Con Γ
      module a = TmS a
      module aS = E.TmS a.E
      module B = TyS B

  --add ΠP

  appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
  appS {Γ}{a}{B} t = record { E  = E.appS t.E
                            ; w' = t.w'
                            ; w  = λ σ α → t.w (E.π₁P {A = E.El a.E} σ) α
                            }
    where
      module Γ = Con Γ
      module a = TmS a
      module B = TyS B
      module t = TmS t
               

