open import Lib
open import AMPDS
open import Syntax using (PS;P;S)

module Wellformedness (Ω : Con) (ŝ : Ω .ᴾ) where

postulate Conʷ : ∀ (Γ : Con) (ν : Sub Ω Γ) → Con.ᴾᴰ Γ (ν .ᴾ ŝ)
postulate TySʷ : ∀ {Γ : Con} (A : Ty Γ S) (ν : Sub Ω Γ) (α : A .ᴾ) → A .ᴾᴰ α
postulate TyPʷ : ∀ {Γ : Con} (A : Ty Γ P) (ν : Sub Ω Γ) (γ : Γ .ᴾ) (γᴾᴰ : Γ .ᴾᴰ γ) (α : A .ᴾ γ) → A .ᴾᴰ γ γᴾᴰ α
--postulate TmSʷ : ∀ {Γ : Con} (A : Ty Γ S) (a : Tm Γ A) →  a .Tm.ᴾᴰ ? ?

∙ʷ : ∀ (ν : Sub Ω ∙) → ∙ .ᴾᴰ (ν .ᴾ ŝ)
∙ʷ ν = lift tt

▶ʷ : ∀ k (Γ : Con) (A : Ty Γ k) (ν : Sub Ω (Γ ▶ A)) → (Γ ▶ A) .ᴾᴰ (ν .ᴾ ŝ)
▶ʷ P Γ A ν = {!!}
▶ʷ S Γ A ν = (Conʷ Γ (π₁ ν) , TySʷ A (π₁ ν) (ν .ᴾ ŝ .₂))


Uʷ : ∀ (Γ : Con) (ν : Sub Ω Γ) (α : U{Γ} .ᴾ) → U{Γ} .ᴾᴰ α
Uʷ Γ ν α x = Set

Elʷ : ∀ (Γ : Con) (a : Tm Γ U) (ν : Sub Ω Γ) (γ : _) (γᴾᴰ : _) (α : (El a) .ᴾ γ) → El a .ᴾᴰ γ γᴾᴰ α
Elʷ Γ a ν γ γᴾᴰ (lift α) = lift {!!}

Πʷ : ∀ (Γ : Con) (a : Tm Γ U) (B : Ty (Γ ▶ El a) S)
       (ν : Sub Ω Γ) (α : (Π a B) .ᴾ) → (Π a B) .ᴾᴰ α
Πʷ Γ a B ν α = let x : Tm Γ (El a)
                   x = {!!} 
               in TySʷ B (ν ,s x [ ν ]t) α --morally (El a .ᴾ (ν .ᴾ ŝ)) → Bʷ ν α
