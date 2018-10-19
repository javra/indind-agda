{-# OPTIONS --without-K #-}

module IIReductionExamples.ConTyIsContr where

open import Lib renaming (_Σ,_ to _,_)

-- Intrinsic models
--------------------------------------------------------------------------------

record Model {ℓ} : Set (suc ℓ) where
  infixl 5 _▶_
  field
    Con  : Set ℓ
    Ty   : Con → Set ℓ
    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con
    U    : (Γ : Con) → Ty Γ
    El   : (Γ : Con) → Ty (Γ ▶ U Γ)
    Π    : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ

record Morphism {ℓ₁}{ℓ₂}(M : Model {ℓ₁})(N : Model {ℓ₂}) : Set (ℓ₁ ⊔ ℓ₂) where
  private module M = Model M
  private module N = Model N
  field
    Con : M.Con → N.Con
    Ty  : ∀{Γ} → M.Ty Γ → N.Ty (Con Γ)
    •   : Con M.∙ ≡ N.∙
    ▶   : ∀{Γ A} → Con (Γ M.▶ A) ≡ Con Γ N.▶ Ty A
    U   : ∀{Γ} → Ty (M.U Γ) ≡ N.U (Con Γ)
    El  : ∀{Γ} → tr (Model.Ty N) (▶ ◾ ap (N Model.▶ Con Γ) U) (Ty (M.El Γ)) ≡ N.El (Con Γ)
    Π   : ∀{Γ A B} → Ty (M.Π Γ A B) ≡ N.Π (Con Γ) (Ty A) (tr N.Ty ▶ (Ty B))

-- Presyntax
--------------------------------------------------------------------------------

infixl 6 _▶_

data Conp : Set
data Typ  : Set

data Conp where
  ∙p   : Conp
  _▶p_ : Conp → Typ → Conp

data Typ where
  Up  : Conp → Typ
  Elp : Conp → Typ
  Πp  : Conp → Typ → Typ → Typ
  
-- Well-formedness predicates
--------------------------------------------------------------------------------

-- It is easy to show that w is propositional, but we don't actually
-- need that proof here. Also, note that Tyw Γ A implies Conw Γ.
Conw : (Γp : Conp) → Set
Tyw  : (Ap : Typ)  → Conp → Set
Conw ∙p = ⊤
Conw (Γp ▶p Ap) = Conw Γp × Tyw Ap Γp
Tyw (Up Γp) Δp = Conw Γp × (Γp ≡ Δp)
Tyw (Elp Γp) Δp = Conw Γp × (Γp ▶p Up Γp ≡ Δp)
Tyw (Πp Γp Ap Bp) Δp = Conw Γp × Tyw Ap Γp × Tyw Bp (Γp ▶p Ap) × (Γp ≡ Δp)

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

syn : Model {zero}
syn = record {
    Con = Σ Conp Conw
  ; Ty  = λ {(Γp , _) → Σ Typ λ Ap → Tyw Ap Γp}
  ; ∙   = ∙p , tt
  ; _▶_ = λ {(Γp , Γw) (Ap , Aw) → (Γp ▶p Ap) , Γw , Aw}
  ; U   = λ {(Γp , Γw) → Up Γp , Γw , refl}
  ; El  = λ {(Γp , Γw) → Elp Γp , Γw , refl}
  ; Π   = λ {(Γp , Γw)(Ap , Aw)(Bp , Bw) → Πp Γp Ap Bp , Γw , Aw , Bw , refl}}

-- module Syn = ConTy ConTySyn

-- Recursion for inductive-inductive syntax
--------------------------------------------------------------------------------

module _ {α}(M : Model {α}) where
  module M = Model M

  -- Logical relation between the presyntax and the M model expressing
  -- that presyntactic and semantic values have the same structure
  Con~ : (Γp : Conp) → M.Con → Set α
  Ty~  : (Ap : Typ)  → Σ M.Con M.Ty → Set α
  Con~ ∙p Γm = Γm ≡ M.∙
  Con~ (Γp ▶p Ap) Δm = Σ M.Con λ Γm → Σ (M.Ty Γm) λ Am → Con~ Γp Γm × Ty~ Ap (Γm , Am) × (Γm M.▶ Am  ≡ Δm)
  Ty~ (Up Γp) (Γm , Am)= Con~ Γp Γm × (M.U Γm ≡ Am)
  Ty~ (Elp Γp) (Δm , Am)= Σ M.Con λ Γm → Con~ Γp Γm × Σ (Γm M.▶ M.U Γm ≡ Δm) λ p → tr M.Ty p (M.El Γm) ≡ Am
  Ty~ (Πp Γp Ap Bp) (Γm , Cm) = Con~ Γp Γm × Σ (M.Ty Γm) λ Am → Σ (M.Ty (Γm M.▶ Am)) λ Bm
                              → Ty~ Ap (Γm , Am) × Ty~ Bp ((Γm M.▶ Am) , Bm) × (M.Π Γm Am Bm ≡ Cm)


  -- Ty~ implies Con~
  TyCon~ : (Γp : Conp) → (Ap : Typ) → Tyw Ap Γp →
     (Γm : M.Con) (Am : M.Ty Γm) → Ty~ Ap (Γm , Am) → Con~ Γp Γm

  TyCon~ Γp (Up .Γp) (Γw , refl) Γm .(M.U  Γm) (Γ~ , refl) = Γ~
  TyCon~ .(Γp ▶p Up Γp) (Elp Γp) (Γw , refl) .(Γm M.▶  (M.U  Γm)) .(M.El Γm) (Γm , Γ~ , refl , refl)
    = Γm , ((M.U Γm) , (Γ~ , ((Γ~ , refl) , refl)))

  TyCon~ Γp (Πp .Γp Ap Ap₁) (Γw , Aw , Bw , refl) Γm Am rA = ₁ rA


  isContr : {l : _} → (A : Set l) → Set l
  isContr A = Σ A λ y → (x : A) → x ≡ y


  center : {l : _} → {A : Set l} → (isCA : isContr A) → A
  center isCA = ₁ isCA

  isContrSingleton : {l : _} → {A : Set l} (x : A) → isContr (Σ A λ y → y ≡ x)
  isContrSingleton x = (x , refl) , λ {(y , refl ) → refl}

  ConC : (Γp : Conp) → Conw Γp → isContr (Σ M.Con λ Γm → Con~ Γp Γm)
  TyC : (Ap : Typ)(Γp : Conp) → Tyw Ap Γp → isContr (Σ M.Con λ Γm → Σ (M.Ty Γm) λ Am → Ty~ Ap (Γm , Am))

  ConC ∙p Γw = isContrSingleton M.∙ 
  -- Σ (Δm Γm : M.Con)(Am : M.Ty Γm), (Γp ~ Γm) × (Ap ~ (Γm, Am)) × (Γm ▶ Am ≡ Δm)
  ConC (Γp ▶p Ap) (Γw , Aw) with TyC Ap Γp Aw
  ...   | Ac , eqAc =
  -- --    Δm
    (((₁ Ac) M.▶ ₁ (₂ Ac)) ,
  -- --    Γm
    ₁ Ac ,
  -- --  Am
    (₁ (₂ Ac)),
    ((TyCon~ Γp Ap Aw (₁ Ac) (₁ (₂ Ac)) (₂ (₂ Ac))) ,
    ₂ (₂ Ac) , refl))
    ,
    λ {(Δm , Γm , Am , rΓ , rA , refl) → {!!}}

  TyC (Up Γp) .Γp (Γw , refl) =
     ((₁ (center (ConC Γp Γw))) ,
     ((M.U (₁ (center (ConC Γp Γw)))) ,
     -- s.t.
     (
     -- (₂ (center (ConC Γp Γw))) ,
     ((₂ (center (ConC Γp Γw))) ,
     refl)))) ,
     -- proof that it is the center
     λ {(Γm , Am , rΓ ,  refl) → {!!}}


  -- Σ (Γm : M.Con)(Am : M.Ty Γm)
  --     (Σ (Δm : M.Con), Γp ~ Δm × Σ (p : Δm ▶ U Δm = Γm) (p # M.El Δm = Am))

  TyC (Elp Γp) .(Γp ▶p Up Γp) (Γw , refl) with (ConC Γp Γw)
  ...    | Γm~ , eqΓm~ =
    ((₁ Γm~ M.▶ M.U (₁ Γm~)) ,
    (M.El (₁ Γm~) ,
      ((₁ Γm~) ,
         ((₂ Γm~) , (refl , refl))))) ,
  -- proof that it is the center
    λ {(Γm , Am , (Em , rEm , refl , refl)
        ) → {!!}}
  
    -- Σ Γm Am ( Γp ~ Γm) × ( Γp ~ Γm) × Σ Bm Cm, Ap ~ (Γm, Bm) × (Bp ~ Γm ▶ Bm, Cm) × M.Π Γm Bm Cm = Am
    -- I would need somewhat to use Γm coming from the center of TyC Bm and Cm.
  TyC (Πp Γp Ap Bp) .Γp (Γw , Aw , Bw , refl) =
    ({!!} ,
    {!!})

-- proof that it is the center
    ,  {!!}




{-
  Con~   ∙           γ = γ ≡ M.∙
  Con~   (Γ ▶ A)     γ = ∃₂ λ γ₀ α → Con~ Γ γ₀ × Ty~ A γ₀ α × (γ ≡ γ₀ M.▶ α)
  Ty~    (U Γ)       γ α = Con~ Γ γ × (α ≡ M.U γ)
  Ty~    (Π Γ A B)   γ α = Con~ Γ γ × ∃₂ λ α₀ α₁ → Ty~ A γ α₀ × Ty~ B (γ M.▶ α₀) α₁ × (α ≡ M.Π γ α₀ α₁)

  -- Semantic values with the same presyntactic structure are equal
  Γ~≡ : (Γ : Con) → ∀ γ γ' → Con~ Γ γ  → Con~ Γ γ' → γ ≡ γ'
  A~≡ : (A : Ty)  → ∀ γ α α' → Ty~ A γ α → Ty~ A γ α' → α ≡ α'
  Γ~≡   ∙           γ γ' ~γ ~γ' = ~γ ◾ ~γ' ⁻¹
  Γ~≡   (Γ ▶ A)     _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                 | refl = ap (γ' M.▶_) (A~≡ A γ α α' ~α ~α')
  A~≡   (U Γ)       γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹
  A~≡   (Π Γ A B)   γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
                          (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl) with A~≡ A γ α₀ α₀' ~α₀ ~α₀'
  ...                 | refl = ap (M.Π γ α₀') (A~≡ B (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

  -- ... which equality is refl in the degenerate case
  Γ~refl : (Γ : Con) → ∀ γ ~γ → Γ~≡ Γ γ γ ~γ ~γ ≡ refl
  A~refl : (A : Ty)  → ∀ γ α ~α → A~≡ A γ α α ~α ~α ≡ refl
  Γ~refl   ∙           γ refl = refl
  Γ~refl   (Γ ▶ A)     _ (γ , α , ~γ , ~α , refl)
                         rewrite Γ~refl Γ γ ~γ | A~refl A γ α ~α = refl
  A~refl   (U Γ)       γ _ (~γ , refl) = refl
  A~refl   (Π Γ A B)   γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
                         rewrite A~refl A γ α₀ ~α₀ | A~refl B (γ M.▶ α₀) α₁ ~α₁ = refl

  -- Interpretation of the well-formed presyntax in M.
  -- We have redundant ~ witnesses, but we must always return the topmost ones,
  -- which is the canonical choice, in order to avoid UIP for recursion.
  ⟦Con⟧ : (Γ : Con) → Conw Γ → ∃ λ γ → Con~ Γ γ
  ⟦Ty⟧  : (A : Ty) → ∀ Γ → Tyw A Γ → ∃₂ λ γ α → Con~ Γ γ × Ty~ A γ α
  ⟦Con⟧   ∙           _ = M.∙ , refl
  ⟦Con⟧   (Γ ▶ A)     (Γw , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl = (γ M.▶ α) , (γ , α , ~γ , ~α , refl)
  ⟦Ty⟧ (U Γ)     _ (Γw , refl) with ⟦Con⟧ Γ Γw
  ...                   | (γ , ~γ) = γ , M.U γ , ~γ , ~γ , refl
  ⟦Ty⟧ (Π Γ A B) Δ (Γw , Aw , Bw , refl) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ...                   | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ...                   | refl with A~≡ A γ'' α α' ~α ~α'
  ...                   | refl = γ , M.Π γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

  -- Recursion
  Conᴿ : Syn.Con → M.Con
  Conᴿ (Γ , Γw) = proj₁ (⟦Con⟧ Γ Γw)

  Tyᴿ : ∀ {Γ} → Syn.Ty Γ → M.Ty (Conᴿ Γ)
  Tyᴿ {Γ , Γw} (A , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | γ , ~γ | γ' , α , ~γ' , ~α with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = α

  ▶ᴿ : ∀ {Γ A} → Conᴿ (Γ Syn.▶ A) ≡ Conᴿ Γ M.▶ Tyᴿ A
  ▶ᴿ {Γ , Γw}{A , Aw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = refl

  Uᴿ : ∀ {Γ} → Tyᴿ (Syn.U Γ) ≡ M.U (Conᴿ Γ)
  Uᴿ {Γ , Γw} with ⟦Con⟧ Γ Γw
  ... | γ , ~γ rewrite Γ~refl Γ γ ~γ = refl

  Πᴿ : ∀ {Γ A B} → Tyᴿ (Syn.Π Γ A B) ≡ M.Π (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
  Πᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ... | refl with A~≡ A γ'' α α' ~α ~α'
  ... | refl rewrite Γ~refl Γ γ'' ~γ = refl

  ConTyRec : ConTyᴿ ConTySyn M
  ConTyRec = record
    { Con = Conᴿ
    ; Ty  = Tyᴿ
    ; •   = refl
    ; ▶   = λ {Γ}{A} → ▶ᴿ {Γ}{A}
    ; U   = λ {Γ} → Uᴿ {Γ}
    ; Π   = λ {Γ}{A}{B} → Πᴿ {Γ}{A}{B}
    }
-}
