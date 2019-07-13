{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import II using (PS; P; S)
open import EWRSg
open import Lib

module TestVec (A : Set) (N : Set) (z : N) (s : N → N)
   (V' : Set) (n' : V') (c' : A → N → V' → V')
   (V : N → Set) (n : V z) (c : A → (n : N) → V n → V (s n)) where

Γ : Con
Γ = ∙ ▶S Π̂S N (λ _ → U)
      ▶P El (âppS vz z)
      ▶P Π̂P A (λ a → Π̂P N (λ n' → ΠP (âppS (vs{S}{P} vz) n') (El (âppS (vs{S}{P} (vs{S}{P} vz)) (s n')))))
{-
Γsg : C'on'.ᴬ Γ
Γsg = C'on'.sg Γ (lift tt , )
               (lift tt , e)
               (lift tt , C'w , Tw)
               (lift tt , ew)
-}

Γwc : _
Γwc = Con.wc Γ {lift tt , V'}
               (lift tt , n' , c')

Γw  : _
Γw  = Con.w Γ {lift tt , V'}
              (lift tt , n' , c')

ΓRc : _
ΓRc = Con.Rc Γ {lift tt , V'}
               (lift tt , n' , c')
               (lift tt , V , n , c)               

ΓR : _
ΓR = Con.R Γ {lift tt , V'}
             (lift tt , n' , c')
             (lift tt , V , n , c)               

