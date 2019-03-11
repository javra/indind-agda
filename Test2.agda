{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import II using (PS; P; S)
open import EWRSgRec
open import Lib

module Test2
   (C : Set) (Cw : C → Set)
   (T : Set) (Tw : C → T → Set)
   (n : C) (nw : Cw n)
   (e : C → T → C) (ew : (Γ : C)(_ : Cw Γ)(A : T)(_ : Tw Γ A) → (Cw (e Γ A)))  where

Γ : Con
Γ = ∙ ▶ U
      ▶S ΠS vz U
      ▶P ΠP (vs {S}{S} vz) (ΠP (appS vz) (El (vsS {P} (vsS {P} (vsS {S} vz))))) -- why do i need to annotate here?

{-Γsg : Con.ᴬ Γ
Γsg = Con.sg Γ (lift tt , C , T)
               (lift tt , e)
               (lift tt , Cw , Tw)
               (lift tt , ew)
-}

Γwc : _
Γwc = Con.wc Γ (lift tt , C , T)

Γw  : _
Γw  = Con.w Γ {lift tt , C , T}
              (lift tt , e)
               
