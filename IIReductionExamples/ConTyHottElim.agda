-- This file is an attempt to show that uniqueness of the recursor is enough to get the eliminator (in extensional type theory)
{-# OPTIONS --without-K  #-}

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
module IIReductionExamples.ConTyHottElim where



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

record Family {ℓ}(M : Model {ℓ}) : Set (Level.suc ℓ) where
  -- infixl 5 _▶_
  private module M = Model {ℓ} M
  field
    Con  : M.Con → Set ℓ
    Ty   : ∀ {Γ : M.Con} → Con Γ → M.Ty Γ → Set ℓ
    ∙    : Con M.∙
    _▶_  : ∀ {Γ : M.Con} (Γf : Con Γ){A : M.Ty Γ}(Af : Ty Γf A) →
      Con (Γ M.▶ A)
    U    : ∀ {Γ}(Γf : Con Γ) → Ty Γf (M.U Γ)
    El   : ∀ {Γ}(Γf : Con Γ) → Ty (_▶_ Γf {M.U Γ} (U Γf)) (M.El Γ)
    ΠΠ    : ∀ {Γ}(Γf : Con Γ){A : M.Ty Γ}(Af : Ty Γf A)
      {B : M.Ty (Γ M.▶ A)} (Bf : Ty (_▶_ Γf {A} Af) B)
        → Ty Γf (M.ΠΠ Γ A B)

record Morphism {ℓ₁}{ℓ₂}(M : Model {ℓ₁})(N : Model {ℓ₂}) : Set (lmax ℓ₁ ℓ₂) where
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


record FamilyMorphism {ℓ₁}(M : Model {ℓ₁})(N : Family M) : Set (lsucc ℓ₁) where
  private module M = Model M
  private module N = Family N
  field
     Con : ∀ Γ → N.Con Γ
     Ty : ∀ {Γ} A → N.Ty (Con Γ) A
     •   : Con M.∙ ≡ N.∙
     ▶   : ∀{Γ A} → Con (Γ M.▶ A) ≡ (Con Γ N.▶ Ty A)
     U   : ∀{Γ} → Ty (M.U Γ) ≡ N.U (Con Γ)
     -- El  : ∀{Γ} → tr (Model.Ty N) (▶ ◾ ap (N Model.▶ Con Γ) U) (Ty (M.El Γ)) ≡ N.El (Con Γ)
     El  : ∀{Γ} → tr (λ x → N.Ty x _) (▶ ◾ ap (Family._▶_ N (Con Γ)) U) (Ty (M.El Γ)) ≡ N.El (Con Γ)
     ΠΠ   : ∀{Γ A B} → Ty (M.ΠΠ Γ A B) ≡ N.ΠΠ (Con Γ) (Ty A) (tr (λ x → N.Ty x _) ▶ (Ty B))

-- Presyntax
--------------------------------------------------------------------------------

infixl 6 _▶_


-- we study the derivability of the dependant eliminator
-- (i.e we want a FamilyMorphism between the syntax and the family M)

module _  {β : _}(syn : Model {β})(M : Family syn)(rec : ∀{α}(N : Model {α}) → is-contr (Morphism syn N))  where
  -- think of [syn] as the syntax  (the initial model)
  module M = Family M
  module S = Model syn

  -- the strategy to define the eliminator is to use the recursor
  -- on the sigma Syntax, Model
  elim-mod : Model 
  elim-mod =
    record
      {
      Con = Σ _ M.Con ;
      Ty = λ x → Σ (S.Ty (₁ x)) λ A → M.Ty (₂ x) A ;
      ∙ = S.∙ , M.∙  ;
      _▶_ = λ Γ A → ((₁ Γ S.▶ ₁ A) ,
        (₂ Γ M.▶ ₂ A ));
      U = λ Γ → (S.U (₁ Γ) , M.U ((₂ Γ))) ;
      El = λ Γ → (S.El (₁ Γ)) , (M.El (₂ Γ)) ;
      ΠΠ = λ Γ A B → S.ΠΠ (₁ Γ)(₁ A)(₁ B) ,
        M.ΠΠ (₂ Γ)(₂ A)(₂ B) 
      }
  

  -- we know that taking the first projection of the following morphism
  -- sigma-rec (which should be given by initiality of the syntax) will yield
  -- an endomorphism of the syntax, and this must be the identity
  -- morphism by initiality. So we give the first projection of this morphism and
  -- see what remains to be given for the second component (this way,
  -- I have less horrible equalities to deal with). We then check
  -- with our brain that what remains to be given is exactly
  -- the components of the family morphism (i.e. the dependent eliminator)
  sigma-rec : Morphism syn elim-mod
  sigma-rec = record
                {
                Con = λ Γ → Γ , Conᴱ Γ ;
                Ty = λ {Γ} A → A , Tyᴱ A  ;
                • = pair= refl ∙ᴱ ;
                ▶ = λ {Γ} {A} → pair= refl (▶ᴱ A) ;
                U = λ {Γ} → pair= refl (Uᴱ Γ) ;
                El = λ {Γ} → pair= (ElS Γ) (Elᴱ Γ) ;
                ΠΠ = λ {Γ}{A}{B} → pair= (ap (S.ΠΠ Γ A) (ΠBS {Γ} A B ))
                  (ΠΠᴱ Γ A B) }
      where
      -- OK means the type agrees with the corresponding field of a family morphism
      -- OK
      Conᴱ : (Γ : S.Con) → M.Con Γ
      -- OK
      Tyᴱ : {Γ : S.Con} (A : S.Ty Γ) → M.Ty (Conᴱ Γ) A
      -- OK
      ∙ᴱ : Conᴱ S.∙ ≡ M.∙
      -- OK
      ▶ᴱ : ∀{Γ} A → Conᴱ (Γ S.▶ A) ≡ (Conᴱ Γ M.▶ Tyᴱ A)
      -- OK
      Uᴱ : ∀ Γ → Tyᴱ (S.U Γ) ≡ M.U (Conᴱ Γ)

      ElS : ∀ Γ → 
        ₁ (coe
        (ap (Model.Ty elim-mod)
        (ap ((Γ S.▶ S.U Γ) ,_) (▶ᴱ (S.U Γ)) ◾
        ap (elim-mod Model.▶ Γ , Conᴱ Γ) (ap (S.U Γ ,_) (Uᴱ Γ))))
        (S.El Γ , Tyᴱ (S.El Γ)))
        ≡ S.El Γ

     -- not OK
      Elᴱ : ∀ Γ → PathOver
        (M.Ty
          (₂
          ((elim-mod Model.▶ Γ , Conᴱ Γ) (Model.U elim-mod (Γ , Conᴱ Γ)))))
          (ElS Γ)
        (₂
          (coe
          (ap (Model.Ty elim-mod)
          (ap ((Γ S.▶ S.U Γ) ,_) (▶ᴱ (S.U Γ)) ◾
          ap (elim-mod Model.▶ Γ , Conᴱ Γ) (ap (S.U Γ ,_) (Uᴱ Γ))))
            (S.El Γ , Tyᴱ (S.El Γ))))
        (M.El (Conᴱ Γ))
    -- here is the OK version
      Elᴱ' : ∀{Γ} → tr (λ x → M.Ty x _) ((▶ᴱ _) ◾ ap (Family._▶_ M (Conᴱ Γ)) (Uᴱ _)) (Tyᴱ (S.El Γ)) ≡ M.El (Conᴱ Γ)
      -- but if I remove the transports (as in extensional type theory), Elᴱ and Elᴱ' have the same type

      ΠBS : ∀ {Γ} A B → B ≡ (₁ (tr (Model.Ty elim-mod) (ap ((Γ S.▶ A) ,_) (▶ᴱ A)) (B , Tyᴱ B)))

      -- not OK
      ΠΠᴱ : ∀ Γ A B → PathOver (M.Ty (Conᴱ Γ)) (ap (S.ΠΠ Γ A) (ΠBS A B))
        (Tyᴱ (S.ΠΠ Γ A B))
        (M.ΠΠ (Conᴱ Γ) (Tyᴱ A)
          (₂
            (tr (Model.Ty elim-mod) (ap ((Γ S.▶ A) ,_) (▶ᴱ A))
              (B , Tyᴱ B))))
     -- this is the OK version
      ΠΠᴱ' : ∀ Γ A B → Tyᴱ (S.ΠΠ Γ A B) ≡ M.ΠΠ (Conᴱ Γ) (Tyᴱ A) (tr (λ x → M.Ty x _) (▶ᴱ _) (Tyᴱ B))
      -- but if I remove the transports (as in extensional type theory), ΠΠᴱ and ΠΠᴱ' have the same type



      Conᴱ = {!!}
      Tyᴱ = {!!}
      ∙ᴱ = {!!}
      ▶ᴱ = {!!}
      Uᴱ = {!!}
      ElS = {!!}
      Elᴱ Γ = {!!}
      Elᴱ' = {!!}
      ΠBS = {!!}
      ΠΠᴱ = {!!}
      ΠΠᴱ' = {!!}


-- In conclusion, it seems that we can derive the dependent eliminator from the uniqueness of the recursor
-- in an extensional type theory
