{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module EWSg where

open import Lib hiding (id; _∘_)
open import II using (PS; P; S)
--import IIA as IIA
import IF as S
open import IFA

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 3 _▶_
infixl 3 _▶S_
infixl 3 _▶P_

record Con : Set₂ where
  field
    Ec  : S.SCon
    E   : S.Con Ec
    wc  : (γc : Ec ᴬc) → (γ : (E ᴬC) γc) → S.SCon
    w   : (γc : Ec ᴬc) → (γ : (E ᴬC) γc) → S.Con (wc γc γ)
    Alg : Set₁
    sg  : (γc : Ec ᴬc) → (γ : (E ᴬC) γc) → (δc : wc γc γ ᴬc) → (δ : (w γc γ ᴬC) δc) → Alg

record TyS (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    w   : {γc : Γ.Ec ᴬc} → (γ : (Γ.E ᴬC) γc) → Set → S.TyS
    Alg : Γ.Alg → Set₁
    sg  : {γc : _} → (γ : (Γ.E ᴬC) γc) → {δc : _} → (δ : (Γ.w γc γ ᴬC) δc) → (α : Set) → (ω : w γ α ᴬS) → Alg (Γ.sg γc γ δc δ)

record TyP (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    E   : S.TyP Γ.Ec
    w   : ∀{γc} → (γ : (Γ.E ᴬC) γc) → (α : (E ᴬP) γc) → S.TyP (Γ.wc γc γ)
    Alg : Γ.Alg → Set
    sg  : {γc : _} → (γ : (Γ.E ᴬC) γc) → {δc : _} → (δ : (Γ.w γc γ ᴬC) δc) → (α : (E ᴬP) γc) → (ω : (w γ α ᴬP) δc) → Alg (Γ.sg γc γ δc δ)

Ty : (Γ : Con) (k : PS) → Set₂
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (A : TyS Γ) : Set₁ where
  module Γ = Con Γ
  module A = TyS A
  field
    E   : S.Tm Γ.Ec S.U
    w   : ∀{γc} → (γ : (Γ.E ᴬC) γc) → S.Tm (Γ.wc γc γ) (A.w γ ((E ᴬt) γc))
    Alg : (γ : Γ.Alg) → A.Alg γ
    sg  : ∀{γc} → (γ : (Γ.E ᴬC) γc) → {δc : _} → (δ : (Γ.w γc γ ᴬC) δc) → Alg (Γ.sg γc γ δc δ) ≡ A.sg γ δ ((E ᴬt) γc) ((w γ ᴬt) δc)

record TmP (Γ : Con) (A : TyP Γ) : Set₁ where
  module Γ = Con Γ
  module A = TyP A
  field
    E   : ∀{γc} → (Con.E Γ ᴬC) γc → (TyP.E A ᴬP) γc
    Alg : (γ : Γ.Alg) → A.Alg γ

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₁
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    Ec  : S.Sub Γ.Ec Δ.Ec
    E   : ∀ γc → LSub Ec Γ.E Δ.E
    wc  : ∀{γc}(γ : (Γ.E ᴬC) γc) → S.Sub (Γ.wc γc γ) (Δ.wc _ (((E γc) ᴬsL) γc γ))
    w   : ∀{γc}(γ : (Γ.E ᴬC) γc){δc}(δ : (Γ.w γc γ ᴬC) δc) → LSub (wc γ) (Γ.w γc γ) (Δ.w _ _)
    Alg : Γ.Alg → Δ.Alg
    sg  : ∀{γc}(γ : _){δc}(δ : _) → Alg (Γ.sg γc γ δc δ) ≡ Δ.sg ((Ec ᴬs) γc) ((E γc ᴬsL) γc γ) ((wc γ ᴬs) δc) ((w γ δ ᴬsL) δc δ)

{- Δ.sg ((Ec ᴬs) γc) ((E γc ᴬsL) γc γ) ((wc γ ᴬs) δc) ((w γ δ ᴬsL) δc δ)
      ≡ Alg (Γ.sg γc γ δc δ)-}

∙ : Con
∙ = record { Ec = S.∙c ; E = S.∙ ; wc = λ _ _ → S.∙c ; w = λ _ _ → S.∙ ; Alg = Lift ⊤ ; sg = λ _ _ _ _ → lift tt }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S A = record { Ec  = Γ.Ec S.▶c S.U ;
                  E   = Γ.E S.▶S S.U ;
                  wc  = λ { (γc , T) γ → (Γ.wc γc γ) S.▶c (A.w γ T) };
                  w   = λ { (γc , T) γ → (Γ.w γc γ) S.▶S (A.w γ T) } ;
                  Alg = Σ Γ.Alg A.Alg ;
                  sg  = λ { (γc , α) γ (δc , ω) δ → Γ.sg γc γ δc δ , A.sg γ δ α ω } }
  where
    module Γ = Con Γ
    module A = TyS A

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { Ec  = Γ.Ec ;
                  E   = Γ.E S.▶P A.E ;
                  wc  = λ { γc (γ , α) → Γ.wc γc γ } ;
                  w   = λ { γc (γ , α) → Γ.w γc γ S.▶P A.w γ α } ;
                  Alg = Σ Γ.Alg A.Alg ;
                  sg  = λ { γc (γ , α) δc (δ , ω) → Γ.sg γc γ δc δ , A.sg γ δ α ω } }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { w   = λ γ T → (T S.⇒̂S S.U) ;
                 Alg = λ γ → Set ;
                 sg  = λ γ δ α ω → Σ α ω }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { E   = S.El a.E ;
                    w   = λ { γ (lift α) → S.El (a.w γ S.$S α) } ;
                    Alg = λ γ → a.Alg γ ;
                    sg  = λ { γ δ (lift α) (lift ω) → coe (a.sg γ δ ⁻¹) (α , ω) } }
  where
    module Γ = Con Γ
    module a = TmS a

ΠS : {Γ : Con} → (a : TmS Γ U) → (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { w   = λ {γc} γ T → S.Π̂S ((a.E ᴬt) γc) (λ α → B.w (γ , lift α) T) ;
                      Alg = λ γ → (α : a.Alg γ) → B.Alg (γ , α) ;
                      sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                          coe (B.Alg & ,≡ refl (coecoe⁻¹' (a.sg γ δ) α))
                                              (B.sg (γ , lift α₁) (δ , lift α₂) πc (π α₁)) }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} → (a : TmS Γ U) → (B : TyP (Γ ▶P El a)) → TyP Γ
ΠP a B = record { E   = a.E S.⇒P B.E ;
                  w   = λ {γc} γ β → S.Π̂P ((a.E ᴬt) γc) (λ τ → (a.w γ S.$S τ) S.⇒P (B.w (γ , lift τ) (β τ))) ;
                  Alg = λ γ → (α : a.Alg γ) → B.Alg (γ , α) ;
                  sg  = λ γ δ πc π α → let (α₁ , α₂) = coe (a.sg γ δ) α in
                                      coe (B.Alg & ,≡ refl (coecoe⁻¹' (a.sg γ δ) α))
                                          (B.sg (γ , lift α₁) (δ , lift α₂) (πc α₁) (π α₁ α₂)) }
  where
    module a = TmS a
    module B = TyP B

Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (t : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {Γ}{a}{B} t = record { E   = t.E ;
                            w   = λ { (γ , lift υ) → t.w γ S.$S υ} ;
                            Alg = λ { (γ , α) → t.Alg γ α } ;
                            sg  = λ { {γc} (γ , lift α) {δc} (δ , ω) →
                                        let (Bs₁ , α') = (B.Γ.sg γc (γ , lift α) δc (δ , ω)) in
                                        let pt : t.Alg (t.A.Γ.sg γc γ δc δ) α' ≡ t.A.sg γ δ ((t.E ᴬt) γc) ((t.w γ ᴬt) δc) α'
                                            pt = happly (t.sg γ δ) α' in
                                        pt ◾ {!!} } }
  where
    module a = TmS a
    module B = TyS B
    module t = TmS t

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { w   = λ {γc} γ → B.w ((σ.E γc ᴬsL) γc γ) ;
                      Alg = λ γ → B.Alg (σ.Alg γ) ;
                      sg  = λ {γc} γ {δc} δ α ω → coe (B.Alg & (σ.sg γ δ ⁻¹))
                                                     (B.sg ((σ.E γc ᴬsL) γc γ) ((σ.w γ δ ᴬsL) δc δ) α ω) }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { E   = A.E S.[ σ.Ec ]T ;
                      w   = λ {γc} γ α →  A.w ((σ.E γc ᴬsL) γc γ) α S.[ σ.wc γ ]T ;
                      Alg = λ γ → A.Alg (σ.Alg γ) ;
                      sg  = λ {γc} γ {δc} δ α ω → coe (A.Alg & (σ.sg γ δ ⁻¹))
                                                     (A.sg ((σ.E γc ᴬsL) γc γ) ((σ.w γ δ ᴬsL) δc δ) α ω) }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS a σ = record { E   = a.E S.[ σ.Ec ]t ;
                      w   = λ {γc} γ → a.w ((σ.E γc ᴬsL) γc γ) S.[ σ.wc γ ]t ;
                      Alg = λ γ → a.Alg (σ.Alg γ) ;
                      sg  = λ {γc} γ {δc} δ → {!!} } -- (a.sg ((σ.E γc ᴬsL) γc γ) ((σ.w γ δ ᴬsL) δc δ))
  where
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP t σ = record { E   = λ {γc} γ → t.E ((σ.E γc ᴬsL) γc γ) ;
                      Alg = λ γ → t.Alg (σ.Alg γ) }
  where
    module t = TmP t
    module σ = Sub σ

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} = _[_]tP
_[_]t {S} = _[_]tS

U[] : ∀{Γ Δ}{δ : Sub Γ Δ} → U [ δ ]TS ≡ U
U[] = refl

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U} → (El a [ σ ]TP) ≡ (El (coe (TmS Γ & (U[] {δ = σ})) (a [ σ ]tS)))
El[] = {!!} --refl

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { Ec  = S.id ;
                  E   = λ γc → Lid ;
                  wc  = λ γ → S.id ;
                  w   = λ γ δ → Lid ;
                  Alg = λ γ → γ ;
                  sg  = λ γ δ → refl }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { Ec  = σ.Ec S.∘ δ.Ec ;
                 E   = λ γ → σ.E ((δ.Ec ᴬs) γ) L∘ δ.E γ ;
                 wc  = λ {γc} γ → σ.wc ((δ.E γc ᴬsL) γc γ) S.∘ δ.wc γ ;
                 w   = λ {γc} γ {δc} δ' → σ.w ((δ.E γc ᴬsL) γc γ) ((δ.w γ δ' ᴬsL) δc δ') L∘ δ.w γ δ' ;
                 Alg = λ γ → σ.Alg (δ.Alg γ) ;
                 sg  = λ {γc} γ {δc} δ' → σ.Alg & δ.sg _ _
                                         ◾ σ.sg ((δ.E γc ᴬsL) γc γ) ((δ.w γ δ' ᴬsL) δc δ') }
  where
    module σ = Sub σ
    module δ = Sub δ

ε : ∀{Γ} → Sub Γ ∙
ε = record { Ec  = S.ε ;
             E   = λ γ → Lε ;
             wc  = λ γ → S.ε ;
             w   = λ γ δ → Lε ;
             Alg = λ _ → lift tt ;
             sg  = λ _ _ → refl }

_,tS_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : TyS Δ} → TmS Γ (A [ σ ]TS) → Sub Γ (Δ ▶S A)
σ ,tS t = record { Ec  = σ.Ec S., t.E ;
                   E   = λ γ → σ.E γ ,S t.E;
                   wc  = λ γ → σ.wc γ S., t.w γ ;
                   w   = λ γ δ → σ.w γ δ ,S t.w γ ;
                   Alg = λ γ → σ.Alg γ , t.Alg γ ;
                   sg  = λ γ δ → ,≡ (σ.sg γ δ) (coe≡ (t.sg γ δ)) }
  where
    module σ = Sub σ
    module t = TmS t

_,tP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
σ ,tP t = record { Ec  = σ.Ec ;
                   E   = λ γ → σ.E γ ,P t.E ;
                   wc  = σ.wc ;
                   w   = λ γ δ → σ.w γ δ ,P λ α → {!!} ;
                   Alg = λ γ → σ.Alg γ , t.Alg γ ;
                   sg  = λ γ δ → ,≡ (σ.sg γ δ) {!!} }
  where
    module σ = Sub σ
    module t = TmP t
    

_,t_ : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,t_ {P} = _,tP_
_,t_ {S} = _,tS_

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ = record { Ec  = S.π₁ σ.Ec ;
                 E   = λ γc → Lπ₁S (σ.E γc) ;
                 wc  = λ γ → S.π₁ (σ.wc γ) ;
                 w   = λ γ δ → Lπ₁S (σ.w γ δ) ;
                 Alg = λ γ → ₁ (σ.Alg γ) ;
                 sg  = λ γ δ → ₁ & σ.sg γ δ }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { Ec  = σ.Ec ;
                 E   = λ γc → Lπ₁P (σ.E γc) ;
                 wc  = σ.wc ;
                 w   = λ γ δ → Lπ₁P (σ.w γ δ) ;
                 Alg = λ γ → ₁ (σ.Alg γ) ;
                 sg  = λ γ δ → ₁ & σ.sg γ δ }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P} = π₁P
π₁ {S} = π₁S

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S σ = record { E   = S.π₂ σ.Ec ;
                 w   = λ γ → S.π₂ (σ.wc γ) ;
                 Alg = λ γ → ₂ (σ.Alg γ) ;
                 sg  = λ γ δ → {!!} }
  where
    module σ = Sub σ

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk {k} = π₁ {k} id

vzS : ∀{Γ}{A : TyS Γ} → TmS (Γ ▶S A) (A [ wk {k = S} ]TS)
vzS = π₂S id

vsS : ∀{k Γ}{A : TyS Γ}{B : Ty Γ k} → TmS Γ A → TmS (Γ ▶ B) (A [ wk {k} ]TS)
vsS {k} t = t [ wk {k} ]tS

vsP : ∀{k Γ}{A : TyP Γ}{B : Ty Γ k} → TmP Γ A → TmP (Γ ▶ B) (A [ wk {k} ]TP)
vsP {k} t = t [ wk {k} ]tP

vs : ∀{k l Γ}{A : Ty Γ k}{B : Ty Γ l} → Tm Γ A → Tm (Γ ▶ B) (A [ wk {l} ]T)
vs {P}{l} t = vsP {l} t
vs {S}{l} t = vsS {l} t

{-
-- Congruence Lemmas

TyS≡ : {Γ : Con}
    {w₀ w₁ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → Set → S.TyS}
    (w₂ : (λ {γc} → w₀ {γc}) ≡ w₁)
  → _≡_ {A = TyS Γ} (record { w = w₀ }) (record { w = w₁ })
TyS≡ refl = refl

TyPw≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)}
    (E₂ : E₀ ≡ E₁)
  → ({γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₀ ᴬP) γc) → S.TyP (Con.wc Γ γc γ))
  ≡ ({γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₁ ᴬP) γc) → S.TyP (Con.wc Γ γc γ))
TyPw≡ refl = refl

coeTyPw≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)} (E₂ : E₀ ≡ E₁)
    {w₀ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₀ ᴬP) γc) → S.TyP (Con.wc Γ γc γ)}
    {w₁ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₁ ᴬP) γc) → S.TyP (Con.wc Γ γc γ)}
    (w₂ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₀ ᴬP) γc) → w₀ γ α ≡ w₁ γ (coe (happly (_ᴬP & E₂) γc) α))
    {γc : _} {γ : (Con.E Γ ᴬC) γc} {α : _}
  → coe (TyPw≡ {Γ = Γ} E₂) w₀ γ α ≡ w₁ γ α
coeTyPw≡ refl w₂ = w₂ _ _
    
TyP≡ : {Γ : Con}
    {E₀ E₁ : S.TyP (Con.Ec Γ)}
    (E₂ : E₀ ≡ E₁)
    {w₀ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₀ ᴬP) γc) → S.TyP (Con.wc Γ γc γ)}
    {w₁ : {γc : Con.Ec Γ ᴬc} → (γ : (Con.E Γ ᴬC) γc) → (α : (E₁ ᴬP) γc) → S.TyP (Con.wc Γ γc γ)}
    (w₂ : (λ {γc} → w₀ {γc}) ≡[ TyPw≡ {Γ = Γ} E₂ ]≡ (λ {γc} → w₁ {γc}))
  → _≡_ {A = TyP Γ} (record { E = E₀ ; w = w₀ }) (record { E = E₁ ; w = w₁ })
TyP≡ refl refl = refl

-- Proofs of the Substitution Laws

[id]T : ∀{k Γ}{A : Ty Γ k} → A [ id ]T ≡ A
[id]T {P}{Γ}{A} = TyP≡ (S.[id]T (TyP.E A))
                     (exti (λ γc → ext λ γ → ext λ α → coeTyPw≡ {Γ}
                       (S.[id]T (TyP.E A)) {w₀ = λ γ₁ α₁ → TyP.w A γ₁ α₁ S.[ S.id ]T} {w₁ = TyP.w A}
                       (λ γ' α' → S.[id]T (TyP.w A γ' α') ◾ (TyP.w A γ') & (coe_refl ⁻¹))))
[id]T {S}       = TyS≡ refl

--[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ} → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
--[][]T {P} = TyP≡ (S.[][]T _ _ _) {!!}
--[][]T {S} = TyS≡ refl

{-
idl   : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idr   : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
ass   : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

,∘    : ∀{k Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ k}{t : Tm Γ (A [ δ ]T)}
      → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
π₁β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → (π₁ (σ ,s t)) ≡ σ
πη    : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)}
      → (π₁ σ ,s π₂ σ) ≡ σ
εη    : ∀{Γ}{σ : Sub Γ ∙}
      → σ ≡ ε
π₂β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = {!!} --σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : TmS Δ U}{B : TyS (Δ ▶P El a)}
      → ((ΠS a B) [ σ ]TS) ≡ (ΠS (a [ σ ]tS) (B [ σ ^ El a ]TS))
Π[] = ?


  app[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))
-}


-}
