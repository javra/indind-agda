{-# OPTIONS --rewriting --allow-unsolved-metas #-}
open import Lib hiding (id; _∘_)
open import IFA
import EWRSgRec as S

module W (X Y : Set₁) (y : Y) (Ω : S.Con) where

  module Ω = S.Con Ω

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
      S : S.Con
      w : (ω : S.Sub Ω S) → _ᵃc {suc zero} (S.Con.Ec S)

  record TyS (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      S : S.TyS Γ.S
      w : Set₁

  record TyP (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      S : S.TyP Γ.S
      w : (ω : S.Sub Ω Γ.S)(t : S.TmP Ω (S S.[ ω ]TP)) → (S.TyP.E S ᵃP) (Γ.w ω)

  record TmS (Γ : Con) (B : TyS Γ) : Set₃ where
    module Γ = Con Γ
    module B = TyS B
    field
      S : S.TmS Γ.S B.S
      w : (ω : S.Sub Ω Γ.S) → B.w ≡ (S.TmS.E S ᵃt) (Γ.w ω)

  record TmP (Γ : Con) (A : TyP Γ) : Set₃ where
    module Γ = Con Γ
    module A = TyP A
    field
      S : S.TmP Γ.S A.S
      w : (ω : S.Sub Ω Γ.S) → A.w ω (S S.[ ω ]tP) ≡ {!!} -- fix univ levels

  ∙ : Con
  ∙ = record { S = S.∙
             ; w = λ ω → lift tt
             }

  _▶S_ : (Γ : Con) → TyS Γ → Con
  Γ ▶S B = record { S = Γ.S S.▶S B.S
                  ; w = λ ω → Γ.w (S.π₁S ω) , B.w
                  }
    where
      module Γ = Con Γ
      module B = TyS B

  _▶P_ : (Γ : Con) → TyP Γ → Con
  Γ ▶P A = record { S = Γ.S S.▶P A.S
                  ; w = λ ω → Γ.w (S.π₁P ω)
                  }
    where
      module Γ = Con Γ
      module A = TyP A

  U : {Γ : Con} → TyS Γ
  U {Γ} = record { S = S.U
                 ; w = Y }
    where
      module Γ = Con Γ

  El : {Γ : Con} (a : TmS Γ U) → TyP Γ
  El {Γ} a = record { S = S.El a.S
                    ; w = λ ω t → coe (a.w ω) y
                    }
    where
      module Γ = Con Γ
      module a = TmS a

  ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
  ΠS {Γ} a B = record { S = S.ΠS a.S B.S
                      ; w = X → B.w
                      }
    where
      module Γ = Con Γ
      module a = TmS a
      module B = TyS B

  --add ΠP

  appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
  appS {Γ}{a}{B} t = record { S = S.appS t.S
                            ; w = λ ω → {!!} ◾ t.w (S.π₁P ω)
                            }
    where
      module Γ = Con Γ
      module a = TmS a
      module B = TyS B
      module t = TmS t
               

