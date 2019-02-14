{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module WR where

open import Lib hiding (id; _∘_)
open import II using (PS; P; S)
import EWSg as E
import AM as AM
import IF as S
open import IFA

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

record Con (ΓE : E.Con) {γc : E.Con.Ec ΓE ᵃc} (γ : (E.Con.E ΓE ᵃC) γc) : Set₂ where
  open E.Con ΓE public
  field
    wc : S.SCon
    w  : S.Con wc

record TyS (ΓE : E.Con) (AE : E.TyS ΓE)
  {γc : E.Con.Ec ΓE ᵃc} (γ : (E.Con.E ΓE ᵃC) γc) (α : Set) (Γ : Con ΓE γ) : Set₂ where
  open E.TyS AE public
  field
    w : S.TyS

record TyP (ΓE : E.Con) (AE : E.TyP ΓE)
  {γc : E.Con.Ec ΓE ᵃc} (γ : (E.Con.E ΓE ᵃC) γc) (α : (E.TyP.E AE ᵃP) γc) (Γ : Con ΓE γ) : Set₂ where
  module Γ  = Con Γ
  open E.TyP AE
  field
    w : S.TyP Γ.wc

∙ : Con E.∙ (lift tt)
∙ = record { wc = S.∙c ;
             w  = S.∙ }
