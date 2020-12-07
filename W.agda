{-# OPTIONS --rewriting --allow-unsolved-metas #-}
open import Lib hiding (id; _∘_)
open import IFA
open import IFD
import E

module W (Ω : E.Con)
  {ωc : _ᵃc {zero} (E.Con.Ec Ω)}(ω : (E.Con.E Ω ᵃC) ωc) where

  module Ω = E.Con Ω


  infixl 7 _[_]TS
  infixl 7 _[_]TP
  --infixl 7 _[_]T
  infix  6 _∘_
  infixl 8 _[_]tS
  infixl 8 _[_]tP
  --infixl 8 _[_]t
  infixl 5 _,tS_
  infixl 5 _,tP_
  --infixl 5 _,t_
  --infixl 3 _▶_
  infixl 3 _▶P_
  infixl 3 _▶S_

  record Con : Set₃ where
    field
      E  : E.Con
      wc : (σ : E.Sub Ω E) → ᵈc {suc zero} (E.Con.Ec E) ((E.Sub.Ec σ ᵃs) ωc)

  record TyS (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      E : E.TyS Γ.E
      w : Set₁ → Set₁

  record TyP (Γ : Con) : Set₃ where
    module Γ = Con Γ
    field
      E : E.TyP Γ.E
      w : ∀(σ : E.Sub Ω Γ.E) α → ᵈP (E.TyP.E E) (Γ.wc σ) α

  record TmS (Γ : Con) (B : TyS Γ) : Set₃ where
    module Γ = Con Γ
    module B = TyS B
    field
      E   : E.TmS Γ.E B.E
      hTy : TyS Γ
      w   : ∀(σ : E.Sub Ω Γ.E) α → ᵈt (E.TmS.E E) (Γ.wc σ) α ≡ {!!}

  record TmP (Γ : Con) (A : TyP Γ) : Set₃ where
    module Γ = Con Γ
    module A = TyP A
    field
      E : E.TmP Γ.E A.E

  record Sub (Γ : Con) (Δ : Con) : Set₂ where
    module Γ = Con Γ
    module Δ = Con Δ
    field
      E : E.Sub Γ.E Δ.E

  ∙ : Con
  ∙ = record { E = E.∙
             }

  _▶S_ : (Γ : Con) → TyS Γ → Con
  Γ ▶S B = record { E  = Γ.E E.▶S B.E
                  ; wc = λ σ → Γ.wc (E.π₁S σ) , λ _ → B.w Set
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
                    ; w = λ σ α → {!!} --coe (a.w σ α ⁻¹) {!!}
                    }
    where
      module Γ = Con Γ
      module a = TmS a

  ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
  ΠS {Γ} a B = record { E = E.ΠS a.E B.E
                      ; w = λ X → B.w X
                      }
    where
      module Γ = Con Γ
      module a = TmS a
      module aS = E.TmS a.E
      module B = TyS B

  ΠP : {Γ : Con} → (a : TmS Γ U) → (A : TyP (Γ ▶P El a)) → TyP Γ
  ΠP {Γ} a A = record { E = E.ΠP a.E A.E
                      ; w = λ σ ϕ α αᵈ → A.w (σ E.,tP {!!}) (ϕ α)
                      }
    where
      module Γ = Con Γ
      module a = TmS a
      module aS = E.TmS a.E
      module A = TyP A

  appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
  appS {Γ}{a}{B} t = record { E    = E.appS t.E
                            ; hTy  = {!!}
                            ; w    = λ σ α → t.w _ α ◾ {!!} --t.w (E.π₁P {A = E.El a.E} σ) α
                            }
    where
      module Γ = Con Γ
      module a = TmS a
      module B = TyS B
      module t = TmS t

  appP : {Γ : Con}{a : TmS Γ U}{B : TyP (Γ ▶P El a)} → (t : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
  appP {Γ}{a}{B} t = record { E = E.appP t.E
                            }
    where
      module a = TmS a
      module B = TyP B
      module t = TmP t

  _[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
  _[_]TS B σ = record { E = B.E E.[ σ.E ]TS
                      ; w = λ X → {!!}
                      }
    where
      module B = TyS B
      module σ = Sub σ

  _[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
  _[_]TP A σ = record { E = A.E E.[ σ.E ]TP
                      ; w = λ δ α → coe {!!} (A.w (σ.E E.∘ δ) α)
                      }
    where
      module A = TyP A
      module σ = Sub σ

  _[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
  _[_]tS {Γ}{Δ}{A} a σ = record { E   = a.E E.[ σ.E ]tS
                                ; hTy = {!!}
                                ; w   = λ δ α → {!!} ◾ a.w (σ.E E.∘ δ) α
                                }
    where
      module A = TyS A
      module a = TmS a
      module σ = Sub σ

  _[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
  _[_]tP {Γ}{Δ}{A} a σ = record { E = a.E E.[ σ.E ]tP
                                }
    where
      module A = TyP A
      module a = TmP a
      module σ = Sub σ

  id : ∀{Γ} → Sub Γ Γ
  id {Γ} = record { E = E.id
                  }
    where
      module Γ = Con Γ

  _∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  σ ∘ δ = record { E = σ.E E.∘ δ.E
                 }
    where
      module σ = Sub σ
      module δ = Sub δ

  ε : ∀{Γ} → Sub Γ ∙
  ε = record { E = E.ε }

  _,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){B : TyS Δ} → TmS Γ (B [ σ ]TS) → Sub Γ (Δ ▶S B)
  σ ,tS t = record { E = σ.E E.,tS t.E }
    where
      module σ = Sub σ
      module t = TmS t

  _,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
  _,tP_ σ {A} t = record { E = σ.E E.,tP t.E }
    where
      module σ = Sub σ
      module A = TyP A
      module t = TmP t

  π₁S : ∀{Γ Δ}{B : TyS Δ} → Sub Γ (Δ ▶S B) → Sub Γ Δ
  π₁S σ = record { E = E.π₁S σ.E }
    where
      module σ = Sub σ

  π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
  π₁P σ = record { E = E.π₁P σ.E }
    where
      module σ = Sub σ

  π₂S : ∀{Γ Δ}{B : TyS Δ}(σ : Sub Γ (Δ ▶S B)) → TmS Γ (B [ π₁S {B = B} σ ]TS)
  π₂S {Γ}{Δ}{B} σ = record { E   = E.π₂S {B = TyS.E B} σ.E
                           ; hTy = {!!}
                           ; w   = λ δ α → {!!}
                           }
    where
      module σ = Sub σ

  π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P {A = A} σ ]TP)
  π₂P {Γ}{Δ}{A} σ = record { E = E.π₂P σ.E }
    where
      module A = TyP A
      module σ = Sub σ
