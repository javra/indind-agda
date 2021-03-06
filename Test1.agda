{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module Test1 (C : Set) (Cw : C → Set)
   (T : Set) (Tw : C → T → Set)
   (n : C) (nw : Cw n)
 where

open import II using (PS; P; S)
open import EWRSg
open import Lib

Γ : Con
Γ = ∙ ▶ U ▶S ΠS vz U ▶P El (vsS {S} vz) -- why do i need to annotate here?

{-
Γsg : Con.ᴬ  Γ
Γsg = Con.sg Γ (lift tt , C , T)
               (lift tt , lift n)
               (lift tt , Cw , Tw)
               (lift tt , lift nw)
-}

Γwc : _
Γwc = Con.wc Γ {lift tt , C , T}
               (lift tt , n)

Γw : _
Γw = Con.w Γ {lift tt , C , T}
             (lift tt , n)
