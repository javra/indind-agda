{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Lib

module StrictLib where

data P⊤ {ℓ} : Prop ℓ where
  ptt : P⊤

data _∧_ {ℓ}(p q : Prop ℓ) : Prop ℓ where
  _,_ : p → q → (p ∧ q)

p₁ : ∀{ℓ}{p q : Prop ℓ} → p ∧ q → p
p₁ (x , y) = x

p₂ : ∀{ℓ}{p q : Prop ℓ} → p ∧ q → q
p₂ (x , y) = y

Pcoe : ∀{ℓ}{A A' : Prop ℓ} → A ≡ A' → A → A'
Pcoe refl a = a

PΠ≡ :
  ∀ {α β}{A A' : Set α}{B : A → Prop β}{B' : A' → Prop β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
PΠ≡ {A = A} {B = B} {B'} refl q = (λ B → (x : A) → B x) & ext q

PPΠ≡ :
  ∀ {α β}{A A' : Prop α}{B : A → Prop β}{B' : A' → Prop β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (Pcoe p a))
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
PPΠ≡ {A = A} {B = B} {B'} refl q = {!!} --(λ B → (x : A) → B x) & pext q

PPΠ≡' :
  ∀ {α β}{A : Prop α}{B B' : A → Prop β} → ((a : A) → B a ≡ B' a)
  → ((a : A) → B a) ≡ ((a' : A) → B' a')
PPΠ≡' {A = A}{B}{B'} q = apd (λ (B : A → Prop _) → (a : A) → B a) {!!}

PΠ≡i :
  ∀ {α β}{A A' : Set α}{B : A → Prop β}{B' : A' → Prop β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ({a : A} → B a) ≡ ({a' : A'} → B' a')
PΠ≡i {A = A}{B = B} refl q = (λ B → {x : A} → B x) & ext q
