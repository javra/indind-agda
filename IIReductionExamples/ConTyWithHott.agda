{-# OPTIONS --without-K #-}

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
module IIReductionExamples.ConTyWithHott where


-- open import Lib renaming (_Σ,_ to _,_)
-- open import Lib renaming (_Σ,_ to _,_)

-- Intrinsic models
--------------------------------------------------------------------------------

record Model {ℓ} : Set (Level.suc ℓ) where
  infixl 5 _▶_
  field
    Con  : Set ℓ
    Ty   : Con → Set ℓ
    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con
    U    : (Γ : Con) → Ty Γ
    El   : (Γ : Con) → Ty (Γ ▶ U Γ)
    ΠΠ    : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ

record Morphism {ℓ₁}{ℓ₂}(M : Model {ℓ₁})(N : Model {ℓ₂}) : Set (lmax ℓ₁ ℓ₂) where
-- record Morphism {ℓ₁}(M : Model {ℓ₁})(N : Model {ℓ₁}) : Set (suc ℓ₁ ) where
  private module M = Model M
  private module N = Model N
  field
    Con : M.Con → N.Con
    Ty  : ∀{Γ} → M.Ty Γ → N.Ty (Con Γ)
    •   : Con M.∙ ≡ N.∙
    ▶   : ∀{Γ A} → Con (Γ M.▶ A) ≡ (Con Γ N.▶ Ty A)
    U   : ∀{Γ} → Ty (M.U Γ) ≡ N.U (Con Γ)
    El  : ∀{Γ} → tr (Model.Ty N) (▶ ◾ ap (N Model.▶ Con Γ) U) (Ty (M.El Γ)) ≡ N.El (Con Γ)
    ΠΠ   : ∀{Γ A B} → Ty (M.ΠΠ Γ A B) ≡ N.ΠΠ (Con Γ) (Ty A) (tr N.Ty ▶ (Ty B))

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
  ΠΠp  : Conp → Typ → Typ → Typ
  
-- Well-formedness predicates
--------------------------------------------------------------------------------

-- It is easy to show that w is propositional, but we don't actually
-- need that proof here. Also, note that Tyw Γ A implies Conw Γ.
Conw : (Γp : Conp) → Set
Tyw  : (Ap : Typ)  → Conp → Set
Conw ∙p = ⊤
Conw (Γp ▶p Ap) = Conw Γp × Tyw Ap Γp
Tyw (Up Γp) Δp = Conw Γp × (Γp ≡ Δp)
Tyw (Elp Γp) Δp = Conw Γp × ((Γp ▶p Up Γp) ≡ Δp)
Tyw (ΠΠp Γp Ap Bp) Δp = Conw Γp × Tyw Ap Γp × Tyw Bp (Γp ▶p Ap) × (Γp ≡ Δp)

-- Conw and Tyw are hprop (needed for the uniqueness of the recursor)
ConwP : (Γp : Conp) → is-prop (Conw Γp)
TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Tyw Ap Γp)

ConwP ∙p = {!!}
ConwP (Γp ▶p Ap) = ×-level (ConwP Γp) (TywP Γp Ap)

-- need to show that the syntax is a hset
TywP Γp (Up Δp) = ×-level (ConwP Δp) {!!}
TywP Γp (ΠΠp Δp Ap Bp) = ×-level (ConwP Δp) (×-level (TywP Δp Ap) (×-level (TywP (Δp ▶p Ap) Bp) {!!}))
TywP Γp (Elp Δp) = ×-level (ConwP Δp) {!!}

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

syn : Model {lzero}
syn = record {
    Con = Σ Conp Conw
  ; Ty  = λ {(Γp , _) → Σ Typ λ Ap → Tyw Ap Γp}
  ; ∙   = ∙p , tt
  ; _▶_ = λ {(Γp , Γw) (Ap , Aw) → (Γp ▶p Ap) , Γw , Aw}
  ; U   = λ {(Γp , Γw) → Up Γp , Γw , refl}
  ; El  = λ {(Γp , Γw) → Elp Γp , Γw , refl}
  ; ΠΠ   = λ {(Γp , Γw)(Ap , Aw)(Bp , Bw) → ΠΠp Γp Ap Bp , Γw , Aw , Bw , refl}}

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
  Con~ (Γp ▶p Ap) Δm = Σ (Σ M.Con (Con~ Γp) ) λ Γm~ → (Σ (Σ (M.Ty (₁ Γm~)) λ Am → ( Ty~ Ap (₁ Γm~ , Am)))
     λ Am~ → ((₁ Γm~ M.▶ ₁ Am~)  ≡ Δm)  ) 
  Ty~ (Up Γp) (Γm , Am)=  (M.U Γm ≡ Am)
  Ty~ (Elp Γp) (Δm , Am)= Σ (Σ M.Con λ Γm → Con~ Γp Γm) λ Γm~ →
     Σ ((₁ Γm~ M.▶ M.U (₁ Γm~)) ≡ Δm) λ p → tr M.Ty p (M.El (₁ Γm~)) ≡ Am
     -- this last equality p will remains when trying to prove the contractibility (TyC)
  
  Ty~ (ΠΠp Γp Ap Bp) (Γm , Cm) =
   Σ (Σ (M.Ty Γm) λ Am → Ty~ Ap (Γm , Am)) λ Am~ →
   Σ (Σ (M.Ty (Γm M.▶ ₁ Am~)) λ Bm → Ty~ Bp ((Γm M.▶ ₁ Am~) , Bm) )
      λ Bm~ →  (M.ΠΠ Γm (₁ Am~) (₁ Bm~) ≡ Cm)



  ConC : (Γp : Conp) → Conw Γp → is-contr (Σ M.Con λ Γm → Con~ Γp Γm)
  TyC : (Ap : Typ)(Γp : Conp) → Tyw Ap Γp → (Γm : M.Con) → Con~ Γp Γm → is-contr (Σ (M.Ty Γm) λ Am → Ty~ Ap (Γm , Am))

  ConC ∙p Γw = pathto-is-contr  M.∙ 
  -- Σ (Δm Γm : M.Con)(A : M.Ty Γm), (Γp ~ Γm) × (Ap ~ (Γm, Am)) × (Γm ▶ Am ≡ Δm)
  ConC (Γp ▶p Ap) (Γw , Aw) = equiv-preserves-level {α} {n = -2}

      ((Σ₁-×-comm {C = λ Γm~ Δm  →
      (Σ (Σ (M.Ty (₁ Γm~)) λ Am → ( Ty~ Ap (₁ Γm~ , Am)))
      λ Am~ → ((₁ Γm~ M.▶ ₁ Am~)  ≡ Δm)  )
      } )
        ∘e
        Σ-emap-r
        λ Γm~ →
        Σ₁-×-comm {C = λ Am~ Δm → ((₁ Γm~ M.▶ ₁ Am~) ≡ Δm)}
       )
       {{ Σ-level
         (ConC Γp Γw)
         λ Γm~ → Σ-level (TyC Ap Γp Aw (₁ Γm~) (₂ Γm~) ) λ Am~ → pathfrom-is-contr  (₁ Γm~ M.▶ ₁ Am~)  }}

  TyC (Up Γp) .Γp (Γw , refl) Γm Γ~ = pathfrom-is-contr (M.U Γm)

  TyC (ΠΠp Γp Ap Bp) .Γp (Γw , Aw , Bw , refl) Γm Γ~ = equiv-preserves-level {α} {n = -2}
      (Σ₁-×-comm {C = λ Am~ Am → Σ (Σ (M.Ty (Γm M.▶ ₁ Am~)) (λ Bm → Ty~ Bp ((Γm M.▶ ₁ Am~) , Bm)))
      (λ Bm~ → M.ΠΠ Γm (₁ Am~) (₁ Bm~) ≡ Am)}
      ∘e
      Σ-emap-r
      
      λ Cm~ →
      Σ₁-×-comm {C = λ Bm~ Am → M.ΠΠ Γm (₁ Cm~) (₁ Bm~) ≡ Am}
      )
      {{ Σ-level (TyC Ap Γp Aw Γm Γ~ )
      λ Am~ → Σ-level
      (TyC Bp (Γp ▶p Ap) Bw (Γm M.▶ ₁ Am~)
      ( (Γm , Γ~) ,  Am~ , refl))
        λ Bm~ → pathfrom-is-contr (M.ΠΠ Γm (₁ Am~) (₁ Bm~))
         }}

  TyC (Elp x) Γp Aw Γm Γ~ = {!!}

  module  _ (mor : Morphism syn M) where
     module F = Morphism mor

     F-Con~ : (Γp : Conp) (Γw : Conw Γp) → Con~ Γp (F.Con (Γp , Γw))
     F-Ty~ : (Γp : Conp) (Γw : Conw Γp)(Ap : Typ) (Aw : Tyw Ap Γp) → Ty~ Ap (F.Con (Γp , Γw) , F.Ty (Ap , Aw))

     F-Con~ ∙p Γw = F.• 
     F-Con~ (Γp ▶p Ap) (Γw , Aw) = (F.Con (Γp , Γw) , F-Con~ Γp Γw) ,
       ((F.Ty (Ap , Aw)) , (F-Ty~ Γp Γw Ap Aw)) , (! F.▶ )

     F-Ty~ Γp Γw (Up .Γp) (Γw' , refl) =
      M.U (F.Con (Γp , Γw))  =⟨  ! F.U  ⟩ ap (λ Γw'' → F.Ty (Up Γp , Γw'' , refl))
     -- I need to prove that Conw is hprop
      (prop-path (ConwP Γp) Γw Γw' ) 
     F-Ty~ Γp Γw (ΠΠp .Γp Ap Bp) (Γw' , Aw , Bw , refl) =
       ((F.Ty (Ap , Aw)) , (F-Ty~ Γp Γw Ap Aw)) ,
       (((tr  M.Ty F.▶  (F.Ty {Γ = ((Γp ▶p Ap) , Γw , Aw)} (Bp , Bw))) ,
       J (λ x e → Ty~ Bp (x , tr M.Ty e (F.Ty (Bp , Bw)))) (F-Ty~ (Γp ▶p Ap) (Γw , Aw) Bp Bw)
         F.▶)
        -- {!F-Ty~ (Γp ▶p Ap) (Γw , Aw) Bp Bw!})
        -- Goal: Ty~ Bp
          -- ((F.Con (Γp , Γw) M.▶ F.Ty (Ap , Aw)) ,
          -- tr M.Ty F.▶ (F.Ty (Bp , Bw)))
        -- Have: Ty~ Bp (F.Con ((Γp ▶p Ap) , Γw , Aw) , F.Ty (Bp , Bw))
       ,  ( M.ΠΠ (F.Con (Γp , Γw)) (F.Ty (Ap , Aw)) (tr M.Ty F.▶ (F.Ty (Bp , Bw)))
               =⟨  ! F.ΠΠ ⟩
               ap (λ Γw'' → F.Ty (ΠΠp Γp Ap Bp , Γw'' , Aw , Bw , refl))
               (prop-path (ConwP Γp) Γw Γw' )) )

     F-Ty~ Γp Γw (Elp x) Aw = {!HoTT.transport!}

   -- uniqueness
     u-F-Con : (Γp : Conp) → (Γw : Conw Γp) →  ₁ (contr-center (ConC Γp Γw)) ≡ F.Con (Γp , Γw) 
     u-F-Con Γp Γw = fst= (contr-path (ConC Γp Γw) (F.Con (Γp , Γw) , F-Con~ Γp Γw ))

     u-F-Ty : (Γp : Conp)  → (Γw : Conw Γp)(Ap : Typ) (Aw : Tyw Ap Γp) →
      ₁ (contr-center (TyC Ap Γp Aw (₁ (contr-center (ConC Γp Γw))) (₂ (contr-center (ConC Γp Γw)))))
        ≡ tr M.Ty (! (u-F-Con Γp Γw)) (F.Ty (Ap , Aw))
     u-F-Ty Γp Γw Ap Aw =
        fst=
           (contr-path (TyC Ap Γp Aw (₁ (contr-center (ConC Γp Γw))) (₂ (contr-center (ConC Γp Γw))))
           (tr M.Ty (! (u-F-Con Γp Γw)) (F.Ty (Ap , Aw)) ,
            J (λ x e → Ty~ Ap (x , tr M.Ty e (F.Ty (Ap , Aw))))
              (F-Ty~ Γp Γw Ap Aw) (! (u-F-Con Γp Γw))
             ))


{-
  Con~   ∙           γ = γ ≡ M.∙
  Con~   (Γ ▶ A)     γ = ∃₂ λ γ₀ α → Con~ Γ γ₀ × Ty~ A γ₀ α × (γ ≡ γ₀ M.▶ α)
  Ty~    (U Γ)       γ α = Con~ Γ γ × (α ≡ M.U γ)
  Ty~    (ΠΠ Γ A B)   γ α = Con~ Γ γ × ∃₂ λ α₀ α₁ → Ty~ A γ α₀ × Ty~ B (γ M.▶ α₀) α₁ × (α ≡ M.ΠΠ γ α₀ α₁)

  -- Semantic values with the same presyntactic structure are equal
  Γ~≡ : (Γ : Con) → ∀ γ γ' → Con~ Γ γ  → Con~ Γ γ' → γ ≡ γ'
  A~≡ : (A : Ty)  → ∀ γ α α' → Ty~ A γ α → Ty~ A γ α' → α ≡ α'
  Γ~≡   ∙           γ γ' ~γ ~γ' = ~γ ◾ ~γ' ⁻¹
  Γ~≡   (Γ ▶ A)     _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                 | refl = ap (γ' M.▶_) (A~≡ A γ α α' ~α ~α')
  A~≡   (U Γ)       γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹
  A~≡   (ΠΠ Γ A B)   γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
                          (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl) with A~≡ A γ α₀ α₀' ~α₀ ~α₀'
  ...                 | refl = ap (M.ΠΠ γ α₀') (A~≡ B (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

  -- ... which equality is refl in the degenerate case
  Γ~refl : (Γ : Con) → ∀ γ ~γ → Γ~≡ Γ γ γ ~γ ~γ ≡ refl
  A~refl : (A : Ty)  → ∀ γ α ~α → A~≡ A γ α α ~α ~α ≡ refl
  Γ~refl   ∙           γ refl = refl
  Γ~refl   (Γ ▶ A)     _ (γ , α , ~γ , ~α , refl)
                         rewrite Γ~refl Γ γ ~γ | A~refl A γ α ~α = refl
  A~refl   (U Γ)       γ _ (~γ , refl) = refl
  A~refl   (ΠΠ Γ A B)   γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
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
  ⟦Ty⟧ (ΠΠ Γ A B) Δ (Γw , Aw , Bw , refl) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ...                   | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ...                   | refl with A~≡ A γ'' α α' ~α ~α'
  ...                   | refl = γ , M.ΠΠ γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

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

  ΠΠᴿ : ∀ {Γ A B} → Tyᴿ (Syn.ΠΠ Γ A B) ≡ M.ΠΠ (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
  ΠΠᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
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
    ; ΠΠ   = λ {Γ}{A}{B} → ΠΠᴿ {Γ}{A}{B}
    }
-}


--
