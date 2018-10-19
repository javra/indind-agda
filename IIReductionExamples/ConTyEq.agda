{-# OPTIONS --without-K #-}

module IIReductionExamples.ConTyEq where

open import Lib

-- intrinsic model

record Model : Set₁ where
  field
    Con : Set
    Ty  : Con → Set
    ∙   : Con
    _▶_ : (Γ : Con)(A : Ty Γ) → Con
    U   : (Γ : Con) → Ty Γ
    El  : (Γ : Con) → Ty (Γ ▶ U Γ)
    Sig : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ
    eq  : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Γ ▶ Sig Γ A B ≡ Γ ▶ A ▶ B

  infixl 6 _▶_

data Conp : Set
data Typ  : Set

data Conp where
  ∙p   : Conp
  _▶p_ : (Γp : Conp)(Ap : Typ) → Conp

infixl 6 _▶p_

data Typ where
  Up   : (Γp : Conp) → Typ
  Elp  : (Γp : Conp) → Typ
  Sigp : (Γp : Conp)(Ap Bp : Typ) → Typ

-- well typedness relation

data Conw : Conp → Set
data Tyw  : Conp → Typ → Set

data Conw where
  ∙w   : Conw ∙p
  _▶w_ : {Γp : Conp}{Ap : Typ}(Γw : Conw Γp)(Aw : Tyw Γp Ap) → Conw (Γp ▶p Ap)

infixl 6 _▶w_

data Tyw where
  Uw   : {Γp : Conp}(Γw : Conw Γp) → Tyw Γp (Up Γp)
  Elw  : {Γp : Conp}(Γw : Conw Γp) → Tyw (Γp ▶p Up Γp) (Elp Γp)
  Sigw : {Γp : Conp}{Ap : Typ}{Bp : Typ}(Γw : Conw Γp)(Aw : Tyw Γp Ap)(Bw : Tyw (Γp ▶p Ap) Bp)
       → Tyw Γp (Sigp Γp Ap Bp)

-- conversion relation

data Con~ : Conp → Conp → Set
data Ty~  : Conp → Typ → Typ → Set

data Con~ where
  symC : {Γp Δp : Conp} → Con~ Γp Δp → Con~ Δp Γp
  tranC : {Γp Δp Θp : Conp} → Con~ Γp Δp → Con~ Δp Θp → Con~ Γp Θp

  ∙~ : Con~ ∙p ∙p
  _▶~_ : {Γp₀ Γp₁ : Conp}{Ap₀ Ap₁ : Typ} → Con~ Γp₀ Γp₁ → Ty~ Γp₀ Ap₀ Ap₁ → Con~ (Γp₀ ▶p Ap₀) (Γp₁ ▶p Ap₁)
  eq~  : {Γp : Conp}{Ap Bp : Typ} → Con~ (Γp ▶p Sigp Γp Ap Bp) (Γp ▶p Ap ▶p Bp)

data Ty~ where
  symT : {Γp : Conp}{Ap Bp : Typ} → Ty~ Γp Ap Bp → Ty~ Γp Bp Ap
  tranT : {Γp : Conp}{Ap Bp Cp : Typ} → Ty~ Γp Ap Bp → Ty~ Γp Bp Cp → Ty~ Γp Ap Cp

  U~   : {Γp₀ Γp₁ : Conp} → Ty~ Γp₀ (Up Γp₀) (Up Γp₁)
  El~  : {Γp₀ Γp₁ : Conp} → Ty~ (Γp₀ ▶p Up Γp₀) (Elp Γp₀) (Elp Γp₁)
  Sig~ : {Γp₀ Γp₁ : Conp}{Ap₀ Ap₁ : Typ}{Bp₀ Bp₁ : Typ} → Ty~ Γp₀ (Sigp Γp₀ Ap₀ Bp₀) (Sigp Γp₁ Ap₁ Bp₁)

module _ (m : Model) where
  private module m = Model m

  Um₌ : {Γm₀ Γm₁ : m.Con}(Γm₌ : Γm₀ ≡ Γm₁)
      → tr m.Ty Γm₌ (m.U Γm₀) ≡ m.U Γm₁
  Um₌ refl = refl

  ▶m₌ : {Γm₀ Γm₁ : m.Con}(Γm₌ : Γm₀ ≡ Γm₁)
        {Am₀ : m.Ty Γm₀}{Am₁ : m.Ty Γm₁}(Am₌ : tr m.Ty Γm₌ Am₀ ≡ Am₁)
      → Γm₀ m.▶ Am₀ ≡ Γm₁ m.▶ Am₁
  ▶m₌ refl refl = refl

  Elm₌ : {Γm₀ Γm₁ : m.Con}(Γm₌ : Γm₀ ≡ Γm₁)
       → tr m.Ty (▶m₌ Γm₌ (Um₌ Γm₌)) (m.El Γm₀) ≡ m.El Γm₁
  Elm₌ refl = refl

  Sigm₌ : {Γm₀ Γm₁ : m.Con}(Γm₌ : Γm₀ ≡ Γm₁)
          {Am₀ : m.Ty Γm₀}{Am₁ : m.Ty Γm₁}(Am₌ : tr m.Ty Γm₌ Am₀ ≡ Am₁)
          {Bm₀ : m.Ty (Γm₀ m.▶ Am₀)}{Bm₁ : m.Ty (Γm₁ m.▶ Am₁)}(Bm₌ : tr m.Ty (▶m₌ Γm₌ Am₌) Bm₀ ≡ Bm₁)
        → tr m.Ty Γm₌ (m.Sig Γm₀ Am₀ Bm₀) ≡ m.Sig Γm₁ Am₁ Bm₁
  Sigm₌ refl refl refl = refl

  ◾C : {Δm₀ Δm₁ Γm₀ Γm₁ : m.Con}(pΔ₀ : Δm₀ ≡ Γm₀)(pΔ₁ : Δm₁ ≡ Γm₁)(Γm₌ : Γm₀ ≡ Γm₁) → Δm₀ ≡ Δm₁
  ◾C refl refl refl = refl

  ◾T : {Δm₀ Δm₁ Γm₀ Γm₁ : m.Con}(pΔ₀ : Δm₀ ≡ Γm₀)(pΔ₁ : Δm₁ ≡ Γm₁)(Γm₌ : Γm₀ ≡ Γm₁)
       {Cm₀ : m.Ty Δm₀}{Cm₁ : m.Ty Δm₁}{Am₀ : m.Ty Γm₀}{Am₁ : m.Ty Γm₁}
       (pC₀ : tr m.Ty pΔ₀ Cm₀ ≡ Am₀)(pC₁ : tr m.Ty pΔ₁ Cm₁ ≡ Am₁)(Am₌ : tr m.Ty Γm₌ Am₀ ≡ Am₁)
     → tr m.Ty (◾C pΔ₀ pΔ₁ Γm₌) Cm₀ ≡ Cm₁
  ◾T refl refl refl refl refl refl = refl

  ≡= : {A : Set}{a₀ a₁ : A}(a₌ : a₀ ≡ a₁){b₀ b₁ : A}(b₌ : b₀ ≡ b₁) → (a₀ ≡ b₀) ≡ (a₁ ≡ b₁)
  ≡= refl refl = refl

  tr2' : {A B : Set}(P : A → B → Set){a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
     → P a₀ b₀ → P a₁ b₁
  tr2' P refl refl x = x

  Σ,0 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
      → _≡_ {A = Σ A B} (a Σ, b) (a' Σ, b') → a ≡ a'
  Σ,0 refl = refl

  Σ,1 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
        (p : _≡_ {A = Σ A B} (a Σ, b) (a' Σ, b')) → tr B (Σ,0 p) b ≡ b'
  Σ,1 refl = refl

  RC : Conp → m.Con → Set
  RT : Typ  → Σ m.Con m.Ty → Set

  record ▶r (Γp : Conp)(Ap : Typ)(Δm : m.Con) : Set where
    inductive
    field
      Γm : m.Con
      Am : m.Ty Γm
      rΓ : RC Γp Γm
      rA : RT Ap (Γm Σ, Am)
      Δ= : Δm ≡ Γm m.▶ Am

  ▶r₌ : {Γp : Conp}{Ap : Typ}
        {Δm₀ : m.Con}{Δm₁ : m.Con}(Δm₌ : Δm₀ ≡ Δm₁)
        {Γm₀ : m.Con}{Γm₁ : m.Con}(Γm₌ : Γm₀ ≡ Γm₁)
        {Am₀ : m.Ty Γm₀}{Am₁ : m.Ty Γm₁}(Am₌ : tr m.Ty Γm₌ Am₀ ≡ Am₁)
        {rΓ₀ : RC Γp Γm₀}{rΓ₁ : RC Γp Γm₁}(rΓ₂ : tr (RC Γp) Γm₌ rΓ₀ ≡ rΓ₁)
        {rA₀ : RT Ap (Γm₀ Σ, Am₀)}{rA₁ : RT Ap (Γm₁ Σ, Am₁)}(rA₌ : tr (RT Ap) (Σ,= Γm₌ Am₌) rA₀ ≡ rA₁)
        {Δ=₀ : Δm₀ ≡ Γm₀ m.▶ Am₀}{Δ=₁ : Δm₁ ≡ Γm₁ m.▶ Am₁}(rΔ=₁ : tr2' _≡_ Δm₌ (▶m₌ Γm₌ Am₌) Δ=₀ ≡ Δ=₁)
      → tr (▶r Γp Ap) Δm₌ (record { Γm = Γm₀ ; Am = Am₀ ; rΓ = rΓ₀ ; rA = rA₀ ; Δ= = Δ=₀} )
      ≡ record { Γm = Γm₁ ; Am = Am₁ ; rΓ = rΓ₁ ; rA = rA₁ ; Δ= = Δ=₁}
  ▶r₌ refl refl refl refl refl refl = refl

  RC ∙p Δm = Δm ≡ m.∙
  RC (Γp ▶p Ap) Δm = ▶r Γp Ap Δm

  RT (Up Γp)        (Γm Σ, Am) = RC Γp Γm × (Am ≡ m.U Γm)
  RT (Elp Γp)       (Δm Σ, Am) = Σ m.Con λ Γm → RC Γp Γm × Σ (Δm ≡ Γm m.▶ m.U Γm) λ p → tr m.Ty p Am ≡ m.El Γm
  RT (Sigp Γp Ap Bp)(Γm Σ, Cm) = RC Γp Γm × Σ (m.Ty Γm) λ Am → Σ (m.Ty (Γm m.▶ Am)) λ Bm
                               → RT Ap (Γm Σ, Am) × RT Bp ((Γm m.▶ Am) Σ, Bm) × (Cm ≡ m.Sig Γm Am Bm)

  isProp : Set → Set
  isProp A = (a b : A) → a ≡ b

  -- RpropC : (Γp : Conp)(Γm₀ Γm₁ : m.Con)(r₀ : RC Γp Γm₀)(r₁ : RC Γp Γm₁)
  --        → Σ (Γm₀ ≡ Γm₁) λ Γm₌ → tr (RC Γp) Γm₌ r₀ ≡ r₁
  -- RpropT : (Ap : Typ)(Γm₀ Γm₁ : m.Con)(Am₀ : m.Ty Γm₀)(Am₁ : m.Ty Γm₁)
  --          (r₀ : RT Ap (Γm₀ Σ, Am₀))(r₁ : RT Ap (Γm₁ Σ, Am₁))
  --        → Σ (Γm₀ ≡ Γm₁) λ Γm₌ → Σ (tr m.Ty Γm₌ Am₀ ≡ Am₁) λ Am₌ → tr (RT Ap) (Σ,= Γm₌ Am₌) r₀ ≡ r₁

--   RpropC ∙p .m.∙ .m.∙ refl refl = refl Σ, refl
--   RpropC (Γp ▶p Ap) .(Γm₀ m.▶ Am₀) .(Γm₁ m.▶ Am₁)
--          (record { Γm = Γm₀ ; Am = Am₀ ; rΓ = rΓ₀ ; rA = rA₀ ; Δ= = refl })
--          (record { Γm = Γm₁ ; Am = Am₁ ; rΓ = rΓ₁ ; rA = rA₁ ; Δ= = refl })
--     with RpropC Γp Γm₀ Γm₁ rΓ₀ rΓ₁ | RpropT Ap Γm₀ Γm₁ Am₀ Am₁ rA₀ rA₁
--   ... | (Γm₌ Σ, rΓ₌) | (Γm₌' Σ, Am₌ Σ, rA₌) = ▶m₌ Γm₌' Am₌ Σ, {!▶r₌ (▶m₌ Γm₌' Am₌) Γm₌' Am₌ rΓ₌!}

--   RpropT = {!!}


-- {-
--   ReqC : (Γp : Conp) → isProp (Σ m.Con λ Γm → RC Γp Γm)
--   ReqT : (Ap : Typ)  → isProp (Σ m.Con λ Γm → Σ (m.Ty Γm) λ Am → RT Ap (Γm Σ, Am))
--   ReqC ∙p (.m.∙ Σ, refl)(.m.∙ Σ, refl) = refl
--   ReqC (Γp ▶p Ap)(.(Γm₀ m.▶ Am₀) Σ, record { Γm = Γm₀ ; Am = Am₀ ; rΓ = rΓ₀ ; rA = rA₀ ; Δ= = refl })
--                  (.(Γm₁ m.▶ Am₁) Σ, record { Γm = Γm₁ ; Am = Am₁ ; rΓ = rΓ₁ ; rA = rA₁ ; Δ= = refl })
--     with ReqC Γp (Γm₀ Σ, rΓ₀)(Γm₁ Σ, rΓ₁) | ReqT Ap (Γm₀ Σ, Am₀ Σ, rA₀)(Γm₁ Σ, Am₁ Σ, rA₁)
--   ... | refl | pA = Σ,= (◾C refl refl (▶m₌ refl {!Σ,0 (Σ,1 pA)!})) {!!}
-- --   ReqC (Γp ▶p Ap)(Δm₀ Σ, Γm₀ Σ, Am₀ Σ, rΓ₀ Σ, rA₀ Σ, pΔ₀)(Δm₁ Σ, Γm₁ Σ, Am₁ Σ, rΓ₁ Σ, rA₁ Σ, pΔ₁) with ReqC Γp (Γm₀ Σ, rΓ₀)(Γm₁ Σ, rΓ₁) | ReqT Ap (Γm₀ Σ, Am₀ Σ, rA₀)(Γm₁ Σ, Am₁ Σ, rA₁)
-- --   ... | pΓ | pA = {!▶r₌ ? ? ? ? ? ? ? ?!}

--   -- with ReqC Γp | ReqT Ap
--   -- ... | Γprop | Aprop = {!!} -- Σ,= (◾C pΔ₀ pΔ₁ (▶m₌ {!Γprop (Γm₀ Σ, rΓ₀)(Γm₁ Σ, rΓ₁)!} {!!})) {!!}

--   ReqT Ap = {!!}
-- -}
-- {-
--   ReqC : (Γp : Conp)(Γm₀ Γm₁ : m.Con)(r₀ : RC Γp Γm₀)(r₁ : RC Γp Γm₁) → Γm₀ ≡ Γm₁
--   ReqT : (Ap : Typ){Γm₀ Γm₁ : m.Con}(Am₀ : m.Ty Γm₀)(Am₁ : m.Ty Γm₁)
--          (r₀ : RT Ap (Γm₀ Σ, Am₀))(r₁ : RT Ap (Γm₁ Σ, Am₁))
--        → Σ (Γm₀ ≡ Γm₁) λ Γm₌ → tr m.Ty Γm₌ Am₀ ≡ Am₁
--   ReqC ∙p Γm₀ Γm₁ r₀ r₁ = ◾C r₀ r₁ refl
--   ReqC (Γp ▶p Ap) Δm₀ Δm₁ (Γm₀ Σ, Am₀ Σ, rΓ₀ Σ, rA₀ Σ, pΔ₀)(Γm₁ Σ, Am₁ Σ, rΓ₁ Σ, rA₁ Σ, pΔ₁) with ReqC Γp Γm₀ Γm₁ rΓ₀ rΓ₁ | ReqT Ap Am₀ Am₁ rA₀ rA₁
--   ... | Γm₌ | (Γm₌' Σ, Am₌) = ◾C pΔ₀ pΔ₁ (▶m₌ Γm₌' Am₌)
--   ReqT (Up Γp){Γm₀}{Γm₁} Am₀ Am₁ (r₀ Σ, pA₀)(r₁ Σ, pA₁) with ReqC Γp _ _ r₀ r₁
--   ... | Γm₌ = ◾C refl refl Γm₌ Σ, ◾T refl refl Γm₌ pA₀ pA₁ (Um₌ Γm₌)
--   ReqT (Elp Γp){Δm₀}{Δm₁} Cm₀ Cm₁ (Γm₀ Σ, r₀ Σ, pΔ₀ Σ, pC₀)(Γm₁ Σ, r₁ Σ, pΔ₁ Σ, pC₁) with ReqC Γp _ _ r₀ r₁
--   ... | pΓ = ◾C pΔ₀ pΔ₁ (▶m₌ pΓ (Um₌ pΓ)) Σ, ◾T pΔ₀ pΔ₁ (▶m₌ pΓ (Um₌ pΓ)) pC₀ pC₁ (Elm₌ pΓ)
--   ReqT (Sigp Γp Ap Bp) Cm₀ Cm₁ (rΓ₀ Σ, Am₀ Σ, Bm₀ Σ, rA₀ Σ, rB₀ Σ, pC₀)(rΓ₁ Σ, Am₁ Σ, Bm₁ Σ, rA₁ Σ, rB₁ Σ, pC₁) with ReqC Γp _ _ rΓ₀ rΓ₁ | ReqT Ap Am₀ Am₁ rA₀ rA₁ | ReqT Bp Bm₀ Bm₁ rB₀ rB₁
--   ReqT (Sigp Γp Ap Bp) {Γm₀}{Γm₁} Cm₀ Cm₁ (rΓ₀ Σ, Am₀ Σ, Bm₀ Σ, rA₀ Σ, rB₀ Σ, pC₀)(rΓ₁ Σ, Am₁ Σ, Bm₁ Σ, rA₁ Σ, rB₁ Σ, pC₁) | pΓ | pΓ' Σ, pA | pΓA Σ, pB
--     = ◾C refl refl pΓ Σ, ◾T refl refl pΓ pC₀ pC₁ {!Sigm₌ pΓ' pA !}

--   RreflC : (Γp : Conp)(Γm : m.Con)(r : RC Γp Γm) → ReqC Γp Γm Γm r r ≡ refl
--   RreflT : (Ap : Typ){Γm : m.Con}(Am : m.Ty Γm)(r : RT Ap (Γm Σ, Am))
--          → ReqT Ap Am Am r r ≡ (refl Σ, refl)


--   RreflC ∙p .m.∙ refl = refl
--   RreflC (Γp ▶p Ap) Γm r = {!!}

--   RreflT = {!!}
-- -}
