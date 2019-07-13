{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import II using (PS; P; S)
open import EWRSg
open import Lib
open import IFA

module TestNat (N' : Set) (z' : N') (s' : N' → N')
  (N : Set) (z : N) (s : N → N) where

Γ : Con
Γ = ∙ ▶S U ▶P El vz ▶P ΠP (vs{S}{P} vz) (El (vs{S}{P} (vs{S}{P} vz)))

{-
Γsg : Con.ᴬ Γ
Γsg = Con.sg Γ (lift tt , )
               (lift tt , e)
               (lift tt , Cw , Tw)
               (lift tt , ew)
-}

Γwc : _
Γwc = Con.wc Γ {lift tt , N}
               (lift tt , z , s)

Γw  : _
Γw  = Con.w Γ {lift tt , N}
              (lift tt , z , s)

ΓRc : _
ΓRc = Con.Rc Γ {lift tt , N'}
               (lift tt , z' , s')
               (lift tt , N , z , s)

ΓR : _
ΓR = Con.R Γ {lift tt , N'}
             (lift tt , z' , s')
             (lift tt , N , z , s)
