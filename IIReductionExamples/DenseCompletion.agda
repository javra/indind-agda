{-# OPTIONS --without-K #-}

module IIReductionExamples.DenseCompletion (A : Set) (_<_ : A → A → Set) where

-- Constructing the recursor for inductive-inductive dense relation completion,
-- using simple mutual induction.

-- Definition of dense completion comes from:
-- https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/talks/Stockholm_2014/indind-2014-06-11.pdf

open import Lib renaming (_Σ,_ to _,_)

-- Intrinsic models & morphisms
--------------------------------------------------------------------------------

record DC {α} : Set (suc α) where
  field
    A+   : Set α
    _<+_ : A+ → A+ → Set α
    ι    : A → A+
    mid  : ∀ {x y} → x <+ y → A+
    ι<   : ∀ {a a'} → a < a' → ι a <+ ι a'
    midₗ : ∀ {x y}(p : x <+ y) → x <+ mid {x}{y} p
    midᵣ : ∀ {x y}(p : x <+ y) → mid {x}{y} p <+ y

record DCᴿ {α β} (M : DC {α})(N : DC {β}) : Set (α ⊔ β) where
  private module M = DC M
  private module N = DC N
  field
    A+   : M.A+ → N.A+
    <+   : ∀ {x y} → x M.<+ y → A+ x N.<+ A+ y
    ι    : ∀ {a} → A+ (M.ι a) ≡ N.ι a
    mid  : ∀ {x y}{p : x M.<+ y} → A+ (M.mid p) ≡ N.mid (<+ p)
    ι<   : ∀ {a a'}{p : a < a'} → coe (ap N._<+_ ι ⊗ ι) (<+ (M.ι< p)) ≡ N.ι< p
    midₗ : ∀ {x y : M.A+}{p : x M.<+ y} → tr (A+ x N.<+_) mid (<+ (M.midₗ p))
                                          ≡ N.midₗ (<+ p)
    midᵣ : ∀ {x y : M.A+}{p : x M.<+ y} → tr (N._<+ A+ y) mid (<+ (M.midᵣ p))
                                          ≡ N.midᵣ (<+ p)
-- Presyntax
--------------------------------------------------------------------------------

data A+ : Set
data <+ : Set

data A+ where
  ι   : A → A+
  mid : A+ → A+ → <+ → A+

data <+ where
  ι<   : ∀ {a a'} → a < a' → <+
  midₗ : A+ → A+ → <+ → <+
  midᵣ : A+ → A+ → <+ → <+

-- Well-formedness
--------------------------------------------------------------------------------

A+w : (x : A+) → Set
<+w : (p : <+) → A+ → A+ → Set

A+w (ι a)       = ⊤
A+w (mid x y p) = A+w x × A+w y × <+w p x y

<+w (ι< {a} {a'} p) xⁱ yⁱ = (ι a ≡ xⁱ) × (ι a' ≡ yⁱ)
<+w (midₗ x y p)    xⁱ yⁱ = A+w x × A+w y × <+w p x y × (x ≡ xⁱ) × (mid x y p ≡ yⁱ)
<+w (midᵣ x y p)    xⁱ yⁱ = A+w x × A+w y × <+w p x y × (mid x y p ≡ xⁱ) × (y ≡ yⁱ)

-- Intrinsic syntax
--------------------------------------------------------------------------------

DCSyn : DC {zero}
DCSyn = record
  { A+   = ∃ A+w
  ; _<+_ = λ {(x , _)(y , _) → ∃ λ p → <+w p x y}
  ; ι    = λ a → ι a , tt
  ; mid  = λ { {x , xw}{y , yw}(p , pw) → mid x y p , xw , yw , pw}
  ; ι<   = λ {a}{a'} p → ι< p , refl , refl
  ; midₗ = λ { {x , xw}{y , yw}(p , pw) → midₗ x y p , xw , yw , pw , refl , refl}
  ; midᵣ = λ { {x , xw}{y , yw}(p , pw) → midᵣ x y p , xw , yw , pw , refl , refl}
  }

module Syn = DC DCSyn

-- Recursion
--------------------------------------------------------------------------------

module _ {α}(M : DC {α}) where
  module M = DC M

  A+~ : (x : A+) → M.A+ → Set α
  <+~ : (p : <+) → ∀ x* y* → x* M.<+ y* → Set α
  A+~ (ι a)       res = M.ι a ≡ res
  A+~ (mid x y p) res = ∃ λ x* → A+~ x x* × ∃ λ y* → A+~ y y* × ∃ λ p* → <+~ p x* y* p* × (M.mid p* ≡ res)

  <+~ (ι< {a}{a'} p) xⁱ yⁱ res = Σ (M.ι a ≡ xⁱ) λ xⁱ= → Σ (M.ι a' ≡ yⁱ) λ yⁱ= →
                                   (coe (ap M._<+_ xⁱ= ⊗ yⁱ=) (M.ι< p) ≡ res)

  -- note : in the midₗ and midᵣ cases below, x* and y* respectively are singleton-contracted away
  <+~ (midₗ x y p)   xⁱ yⁱ res = A+~ x xⁱ × ∃ λ y* → A+~ y y* × ∃ λ p* → <+~ p xⁱ y* p* ×
                                 Σ (M.mid p* ≡ yⁱ) λ yⁱ= → (tr (xⁱ M.<+_) yⁱ= (M.midₗ p*) ≡ res)
  <+~ (midᵣ x y p)   xⁱ yⁱ res = ∃ λ x* → A+~ x x* × A+~ y yⁱ × ∃ λ p* → <+~ p x* yⁱ p* ×
                                 Σ (M.mid p* ≡ xⁱ) λ xⁱ= → (tr (M._<+ yⁱ) xⁱ= (M.midᵣ p*) ≡ res)

  A+~≡ : (x : A+) → ∀ x* x*' → A+~ x x* → A+~ x x*' → x* ≡ x*'
  <+~≡ : (p : <+) → ∀ xⁱ yⁱ xⁱ' yⁱ' p* p*' → <+~ p xⁱ yⁱ p* → <+~ p xⁱ' yⁱ' p*'
         → Σ (xⁱ ≡ xⁱ') λ xⁱ= → Σ (yⁱ ≡ yⁱ') λ yⁱ= → coe (ap M._<+_ xⁱ= ⊗ yⁱ=) p* ≡ p*'
  A+~≡ (ι x)       xⁱ xⁱ' ~x ~x' = ~x ⁻¹ ◾ ~x'
  A+~≡ (mid x y p) _  _  (x*  , ~x  , y*  , ~y  , p*  , ~p  , refl)
                         (x*' , ~x' , y*' , ~y' , p*' , ~p' , refl)
                         with <+~≡ p x* y* x*' y*' p* p*' ~p ~p'
  ... | (refl , refl , refl) = refl
  <+~≡ (ι< p)       xⁱ yⁱ xⁱ' yⁱ' p* p*' (refl , refl , refl) ~p' = ~p'
  <+~≡ (midₗ x y p) xⁱ yⁱ xⁱ' yⁱ' pⁱ pⁱ'
                   (~x  , y*  , ~y  , p*  , ~p  , refl , refl )
                   (~x' , y*' , ~y' , p*' , ~p' , refl , refl )
    with <+~≡ p xⁱ y* xⁱ' y*' p* p*' ~p ~p'
  ... | refl , refl , refl = refl , refl , refl
  <+~≡ (midᵣ x y p) xⁱ yⁱ xⁱ' yⁱ' pⁱ pⁱ'
                   (x*  , ~x  , ~y  , p*  , ~p  , refl , refl )
                   (x*' , ~x' , ~y' , p*' , ~p' , refl , refl )
    with <+~≡ p x* yⁱ x*' yⁱ' p* p*' ~p ~p'
  ... | refl , refl , refl = refl , refl , refl

  A+~refl : ∀ (x : A+) x* ~x → A+~≡ x x* x* ~x ~x ≡ refl
  <+~refl : ∀ p xⁱ yⁱ p* ~p → <+~≡ p xⁱ yⁱ xⁱ yⁱ p* p* ~p ~p ≡ (refl , refl , refl)

  A+~refl (ι x)       _  refl = refl
  A+~refl (mid x y p) xⁱ (x* , ~x , y* , ~y , p* , ~p , refl) rewrite <+~refl p x* y* p* ~p = refl
  <+~refl = {!!}
  -- Agda 2.5.4 doesn't want this (2.5.3 did):
  -- <+~refl (ι< p)       xⁱ yⁱ p* (refl , refl , refl) = refl
  -- <+~refl (midₗ x y p) xⁱ yⁱ p* (~x  , y*  , ~y  , p*  , ~p  , refl , refl ) = ?
  --   rewrite <+~refl p xⁱ y* p* ~p = refl
  -- <+~refl (midᵣ x y p) xⁱ yⁱ p* (x*  , ~x  , ~y  , p*  , ~p  , refl , refl )
  --   rewrite <+~refl p x* yⁱ p* ~p = refl

  ⟦A+⟧ : (x : A+) → A+w x → ∃ (A+~ x)
  ⟦<+⟧ : (p : <+) → ∀ x y → <+w p x y → ∃ λ x* → A+~ x x* × ∃ λ y* → A+~ y y* × ∃ (<+~ p x* y*)

  ⟦A+⟧ (ι a) xw = M.ι a , refl
  ⟦A+⟧ (mid x y p) (xw , yw , pw) with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl = M.mid p* , x* , ~x , y* , ~y' , p* , ~p , refl
  ⟦<+⟧ (ι< {a}{a'} p) _ _ (refl , refl) =
    M.ι a , refl , M.ι a' , refl , M.ι< p , refl , refl , refl

  ⟦<+⟧ (midₗ x y p) _ _ (xw , yw , pw , refl , refl)
    with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl =
    x* , ~x , M.mid p* , (x* , ~x , y* , ~y , p* , ~p , refl)
    , M.midₗ p* , ~x' , y* , ~y' , p* , ~p , refl , refl

  ⟦<+⟧ (midᵣ x y p) _ _ (xw , yw , pw , refl , refl)
    with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl =
    M.mid p* , (x* , ~x , y* , ~y , p* , ~p , refl) , y* , ~y ,
    M.midᵣ p* , x* , ~x , ~y' , p* , ~p , refl , refl

  A+ᴿ : Syn.A+ → M.A+
  A+ᴿ (x , xw) = ₁ (⟦A+⟧ x xw)

  <+ᴿ : ∀ {x y} → x Syn.<+ y → A+ᴿ x M.<+ A+ᴿ y
  <+ᴿ {x , xw}{y , yw} (p , pw) with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl = p*

  ιᴿ : ∀ {a} → A+ᴿ (Syn.ι a) ≡ M.ι a
  ιᴿ {a} = refl

  midᴿ : ∀ {x y p} → A+ᴿ (Syn.mid {x}{y} p) ≡ M.mid (<+ᴿ {x}{y} p)
  midᴿ {x , xw}{y , yw}{p , pw} with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl = refl

  ι<ᴿ : ∀ {a a' p} → <+ᴿ (Syn.ι< {a}{a'} p) ≡ M.ι< p
  ι<ᴿ {a}{a'}{p} = refl

  midₗᴿ : ∀ {x y p} → tr (M._<+_ (A+ᴿ x)) (midᴿ{x}{y}{p}) (<+ᴿ (Syn.midₗ {x}{y} p)) ≡ M.midₗ (<+ᴿ p)
  midₗᴿ {x , xw}{y , yw}{p , pw} with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl rewrite <+~refl p x* y* p* ~p | A+~refl x x* ~x = refl

  midᵣᴿ : ∀ {x y p} →  tr (M._<+ A+ᴿ y) (midᴿ {x}{y}{p}) (<+ᴿ (Syn.midᵣ {x}{y} p)) ≡ M.midᵣ (<+ᴿ p)
  midᵣᴿ {x , xw}{y , yw}{p , pw} with ⟦A+⟧ x xw | ⟦A+⟧ y yw | ⟦<+⟧ p x y pw
  ... | x* , ~x | y* , ~y | x*' , ~x' , y*' , ~y' , p* , ~p
    with A+~≡ x _ _ ~x ~x' | A+~≡ y _ _ ~y ~y'
  ... | refl | refl rewrite <+~refl p x* y* p* ~p | A+~refl y y* ~y = refl

  DCRec : DCᴿ DCSyn M
  DCRec = record
    { A+   = A+ᴿ
    ; <+   = λ {x}{y} → <+ᴿ {x}{y}
    ; ι    = λ {a} → ιᴿ {a}
    ; mid  = λ {x}{y}{p} → midᴿ {x}{y}{p}
    ; ι<   = λ {a}{a'}{p} → ι<ᴿ {a}{a'}{p}
    ; midₗ = λ {x}{y}{p} → midₗᴿ {x}{y}{p}
    ; midᵣ = λ {x}{y}{p} → midᵣᴿ {x}{y}{p}
    }
