{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module Test1 (C : Set) (Cw : C → Set)
   (T : Set) (Tw : C → T → Set)
   (n : C) (nw : Cw n)
   (u : T) (uw : Tw n u) where

open import II using (PS; P; S)
open import EWSg
open import Lib

Γ : Con
Γ = ∙ ▶ U ▶S ΠS vz U ▶P El (vsS {S} vz) ▶P El (appS (vs{S}{S} vz) vz) -- why do i need to annotate here?
  
Γsg : Con.Alg Γ
Γsg = Con.sg Γ (lift tt , C , T)
               (lift tt , lift n , lift u)
               (lift tt , Cw , Tw)
               (lift tt , lift nw , lift uw)

