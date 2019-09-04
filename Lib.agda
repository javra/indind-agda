{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module Lib where

open import Level public
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Data.Empty public

{-# BUILTIN REWRITE _≡_ #-}
postulate cheat : ∀ {α}{A : Set α} → A

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

infixr 9 _∘_
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ p = p
infixr 4 _◾_

◾refl : ∀ {i}{A : Set i}{x y : A}(p : x ≡ y) → (p ◾ refl) ≡ p
◾refl refl = refl
{-# REWRITE ◾refl #-}

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
infix 6 _⁻¹

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_&_ :
  ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → f a₀ ≡ f a₁
f & refl = refl
infixl 9 _&_

id& : ∀{i}{A : Set i}{a₀ a₁ : A}(p : a₀ ≡ a₁) → id & p ≡ p
id& refl = refl
{-# REWRITE id& #-}

const& :
  ∀ {i j}{A : Set i}{B : Set j}{a₀ a₁ : A}(p : a₀ ≡ a₁){b : B}
  → (λ _ → b) & p ≡ refl
const& refl = refl
{-# REWRITE const& #-}

&& : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{f : A → B}{g : B → C}
       {a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → (λ x → g (f x)) & a₂ ≡ g & (f & a₂)
&& refl = refl

coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
       → coe p (coe q a) ≡ coe (q ◾ p) a
coe∘ refl refl _ = refl

coecoe⁻¹ : ∀ {i}{A B : Set i}(p : A ≡ B) x → coe p (coe (p ⁻¹) x) ≡ x
coecoe⁻¹ refl x = refl

coecoe⁻¹' : ∀ {i}{A B : Set i}(p : A ≡ B) x → coe (p ⁻¹) (coe p x) ≡ x
coecoe⁻¹' refl x = refl

tr : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B p = coe (B & p)

tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀}{.a₀} refl refl c₀ = c₀

happly : ∀ {α β}{A : Set α}{B : A → Set β}{f g : (a : A) → B a} → f ≡ g → ∀ a → f a ≡ g a
happly refl a = refl

happly2 : ∀{i j k}{A : Set i}{B : Set j}{C : B → Set k}(f : A → (b : B) → C b)
          {a a' : A}(p : a ≡ a')(b : B)
          → f a b ≡ f a' b
happly2 f refl b = refl

&⁻¹ : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      → f & a₂ ⁻¹ ≡ f & (a₂ ⁻¹)
&⁻¹ f refl = refl

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → coe (B & a₂) (f a₀) ≡ f a₁
apd f refl = refl

apd' : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁){q : B a₀ ≡ B a₁}
    → coe q (f a₀) ≡ f a₁
apd' f refl {refl} = refl

J :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → P x refl → {y : A} → (w : x ≡ y) → P y w
J P pr refl = pr

J⁻¹ :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → {y : A} → (w : x ≡ y) → P y w → P x refl
J⁻¹ P refl p = p

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
infixl 5 _,_

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
, y = _ , y

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B
infixr 4 _×_

,≡ : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → coe (B & p) b ≡ b' → (Σ A B ∋ (a , b)) ≡ (a' , b')
,≡ refl refl = refl

{-coe,≡ : ∀{i j k}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → (q : coe (B & p) b ≡ b')
     {C : Σ A B → Set k}{c : C (a , b)}
     → coe (C & ,≡ p q) c ≡ coe (C & ({!!} ◾ (λ x → a' , x) & q)) c
coe,≡ = {!!}-}

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

record ⊤ : Set where
  constructor tt

data _⊎_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

either : ∀{i j k}{A : Set i}{B : Set j}{C : Set k} → (A → C) → (B → C) → A ⊎ B → C
either f g (inl x) = f x
either f g (inr x) = g x

ind⊎ : ∀{i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k)
       → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor mkReveal
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = mkReveal refl

Π≡ :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
Π≡ {A = A} {B = B} {B'} refl q = (λ B → (x : A) → B x) & ext q

Π≡i :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ({a : A} → B a) ≡ ({a' : A'} → B' a')
Π≡i {A = A}{B = B} refl q = (λ B → {x : A} → B x) & ext q

-- Pathovers

_≡[_]≡_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ α ]≡ y = ((coe α x) ≡ y)

infix 4 _≡[_]≡_

coh : ∀{ℓ}{A B : Set ℓ}(p : A ≡ B) → (a : A) → a ≡[ p ]≡ coe p a
coh refl a = refl

[_]_◾_ : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}
         (f : (x : A) → B x)(p : b ≡ f a)(q : a ≡ a')
       → b ≡[ B & q ]≡ f a'
[ f ] refl ◾ refl = refl

coe-refl : ∀{ℓ}{A : Set ℓ}{p : A ≡ A}{a : A} → coe p a ≡ a
coe-refl {p = refl} = refl

coe-coe : ∀ {i}{A B : Set i}(p q : A ≡ B)(x : A) → coe p x ≡ coe q x
coe-coe refl refl x = refl

coe≡ : ∀{ℓ}{A B : Set ℓ}{p : A ≡ B}{q : B ≡ A} → {a : A} → {b : B}
  → a ≡ coe q b
  → coe p a ≡ b
coe≡ {p = refl}{q = refl} r = r

coe≡' : ∀{ℓ}{A B : Set ℓ}{p : A ≡ B}{q : B ≡ A} → {a : A} → {b : B}
  → coe p a ≡ b
  → a ≡ coe q b
coe≡' {p = refl}{q = refl} r = r

coehapply2 : ∀{ℓ}{A A' B : Set ℓ}(f : A → B)(q : A ≡ A')
  → coe(happly2 (λ A B → A → B) q B) f ≡ λ a' → f (coe (q ⁻¹) a')
coehapply2 {ℓ} {A} {.A} {B} f refl = refl

aptot : ∀{ℓ}{A : Set ℓ}{B : A → Set}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → _≡_ {A = Σ Set λ X → X} (B a₀ , f a₀) (B a₁ , f a₁)
aptot f refl = refl

,= : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → b ≡[ B & p ]≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
,= refl refl = refl

,=1 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
    → _≡_ {A = Σ A B} (a , b) (a' , b') → a ≡ a'
,=1 = λ p → ₁ & p

,=2 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{x y : Σ A B}
      (p : x ≡ y) → (q : ₁ x ≡ ₁ y) → ₂ x ≡[ B & q ]≡ ₂ y
,=2 {B = B} {x} {.x} refl refl = refl

Σ≡ : ∀{ℓ ℓ'}
     {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
     {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : B₀ ≡[ (λ z → z → Set ℓ') & A₂ ]≡ B₁)
   → Σ A₀ B₀ ≡ Σ A₁ B₁
Σ≡ refl refl = refl

×≡ : ∀{ℓ ℓ'}{A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁){B₀ B₁ : Set ℓ'}(B₂ : B₀ ≡ B₁)
  → (A₀ × B₀) ≡ (A₁ × B₁)
×≡ refl refl = refl

irrel : ∀{ℓ}{A : Set ℓ}{a₀ a₁ : A}(p₀ p₁ : a₀ ≡ a₁) → p₀ ≡ p₁
irrel refl refl = refl

Lift-irrel : ∀{ℓ ℓ'}{A : Set ℓ}{a₀ a₁ : A}(p₀ p₁ : Lift ℓ' (a₀ ≡ a₁)) → p₀ ≡ p₁
Lift-irrel (lift refl) (lift refl) = refl

≡≡ : ∀{ℓ}{A : Set ℓ}{a₀ a₀' a₁ a₁' : A}(p : a₀ ≡ a₀')(q : a₁ ≡ a₁')
  → (a₀ ≡ a₁) ≡ (a₀' ≡ a₁')
≡≡ refl refl = refl

coe→ : ∀{ℓ ℓ'}{A : Set ℓ}{B₀ B₁ : A → Set ℓ'}(f : (a : A) → B₀ a)(a : A)
  (p : ((a : A) → B₀ a) ≡ ((a : A) → B₁ a)) (q : B₀ a ≡ B₁ a) (r : B₀ ≡ B₁)
  → (coe p f) a ≡ coe q (f a)
coe→ f a refl refl refl = refl

fcoe : ∀{ℓ ℓ'}{A A' : Set ℓ}{B : A → Set ℓ'}(f : (a : A) → B a){a : A'} p p' q
  → f (coe p a) ≡ coe q (f (coe p' a))
fcoe f refl refl refl = refl

{-
,Σ=η : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{w w' : Σ A B}
      (p : w ≡ w') → ,Σ= (,Σ=0 p) (,Σ=1 p) ≡ p
,Σ=η refl = refl

,Σ=β0 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b') → ,Σ=0 (,Σ= p q) ≡ p
,Σ=β0 refl refl = refl

,Σ=β1 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b')
     → ,Σ=1 (,Σ= p q) ≡[ ap (λ r → b ≡[ ap B r ]≡ b') (,Σ=β0 p q) ]≡ q
,Σ=β1 refl refl = refl

,Σ=2 : {A : Set}{B : A → Set}{a : A}{b : B a}
       {α : a ≡ a}{β : b ≡[ ap B α ]≡ b}
     → (w : α ≡ refl) → β ≡[ ap (λ γ → b ≡[ ap B γ ]≡ b) w ]≡ refl
     → ,Σ= α β ≡ refl
,Σ=2 refl refl = refl

,Σ==
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}
    {a₀ a₁ : A}{b₀ : B a₀}{b₁ : B a₁}
    {p₀ p₁ : a₀ ≡ a₁}(p₂ : p₀ ≡ p₁)
    {q₀ : b₀ ≡[ ap B p₀ ]≡ b₁}{q₁ : b₀ ≡[ ap B p₁ ]≡ b₁}(q₂ : q₀ ≡[ ≡= refl {a₀ = coe (ap B p₀) b₀}{coe (ap B p₁) b₀} (ap (λ z → coe (ap B z) b₀) p₂) refl ]≡ q₁) -- xxx
  → _≡_ (,Σ= p₀ q₀) (,Σ= p₁ q₁)
,Σ== refl refl = refl
-}
