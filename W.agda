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
      w : (ω : S.Sub Ω Γ.S)(t : S.TmS Ω (S S.[ ω ]TS)) → Set₁


  ∙ : Con
  ∙ = record { S = S.∙
             ; w = λ ω → lift tt
             }

  _▶S_ : (Γ : Con) → TyS Γ → Con
  Γ ▶S B = record { S = Γ.S S.▶S B.S
                  ; w = λ ω → Γ.w (S.π₁S ω) , B.w (S.π₁S ω) (S.π₂S ω)
                  }
    where
      module Γ = Con Γ
      module B = TyS B
               

