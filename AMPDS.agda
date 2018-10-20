

module AMPDS where

open import Lib hiding (id; _∘_)
open import Syntax using (PS;P;S)

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 3 _▶_

i : Level
i = suc (suc zero)

j : Level
j = suc zero

record Con : Set i where
  constructor mkCon
  field
    ᴬ  : Set₁
    ᴹ  : ᴬ → ᴬ → Set₁
    ᴾ  : Set₁                 -- prealg
    ᴾᴰ : ᴾ → Set₁             -- displayed prealg
    ᴾˢ : (γ : ᴾ) → ᴾᴰ γ → Set -- displayed prealg section
open Con public

Tyᴾ : ∀ {k : PS}(Γ : Con) → Set₂
Tyᴾ {P} Γ = Γ .ᴾ → Set₁
Tyᴾ {S} Γ = Set₁

Tyᴾᴰ : ∀ {k : PS}(Γ : Con) → Tyᴾ {k} Γ → Set₂
Tyᴾᴰ {P} Γ Aᴾ = (γ : Con.ᴾ Γ) → Con.ᴾᴰ Γ γ → Aᴾ γ → Set₁
Tyᴾᴰ {S} Γ Aᴾ = Aᴾ → Set₁

Tyᴾˢ : ∀ {k : PS}(Γ : Con){Aᴾ : Tyᴾ {k} Γ}(Aᴾᴰ : Tyᴾᴰ {k} Γ Aᴾ) → Set₁
Tyᴾˢ {P} Γ {Aᴾ} Aᴾᴰ = {γᴾ : Γ .ᴾ}(γᴾᴰ : Γ .ᴾᴰ γᴾ)(γˢ : Γ .ᴾˢ γᴾ γᴾᴰ)
                    → (α : Aᴾ γᴾ) → Aᴾᴰ γᴾ γᴾᴰ α → Set
Tyᴾˢ {S} Γ {Aᴾ} Aᴾᴰ = (α : Aᴾ) → Aᴾᴰ α → Set

record Ty (Γ : Con)(k : PS) : Set i where
  constructor mkTy
  field
    ᴬ  : Γ .ᴬ → Set₁
    ᴹ  : ∀ {γ₀ γ₁} → Γ .ᴹ γ₀ γ₁ → ᴬ γ₀ → ᴬ γ₁ → Set
    ᴾ  : Tyᴾ {k} Γ
    ᴾᴰ : Tyᴾᴰ {k} Γ ᴾ
    ᴾˢ : Tyᴾˢ {k} Γ ᴾᴰ
open Ty public

Tmᴾ : ∀ {Γ}{k}(A : Ty Γ k) → Set₁
Tmᴾ {Γ} {P} A = (γ : Γ .ᴾ) → A .ᴾ γ
Tmᴾ {Γ} {S} A = Γ .ᴾ → A .ᴾ

Tmᴾᴰ : ∀ {Γ}{k}(A : Ty Γ k) → Tmᴾ {Γ}{k} A → Set₁
Tmᴾᴰ {Γ} {P} A tᴾ = (γ : Γ .ᴾ)(γᴾᴰ : Γ .ᴾᴰ γ) → A .ᴾᴰ γ γᴾᴰ (tᴾ γ)
Tmᴾᴰ {Γ} {S} A tᴾ = (γ : Γ .ᴾ) → Γ .ᴾᴰ γ → A .ᴾᴰ (tᴾ γ)

Tmᴾˢ : ∀ {Γ}{k}(A : Ty Γ k){tᴾ : Tmᴾ {Γ}{k} A} → Tmᴾᴰ {Γ}{k} A tᴾ → Set₁
Tmᴾˢ {Γ} {P} A {tᴾ} tᴾᴰ =
  (γ : Γ .ᴾ)(γᴾᴰ : Γ .ᴾᴰ γ)(γᴾˢ : Γ .ᴾˢ γ γᴾᴰ)
  → A .ᴾˢ γᴾᴰ γᴾˢ (tᴾ γ) (tᴾᴰ γ γᴾᴰ)
Tmᴾˢ {Γ} {S} A {tᴾ} tᴾᴰ =
  (γ : Γ .ᴾ)(γᴾᴰ : Γ .ᴾᴰ γ) → Γ .ᴾˢ γ γᴾᴰ → A .ᴾˢ (tᴾ γ) (tᴾᴰ γ γᴾᴰ)

record Tm (Γ : Con){k}(A : Ty Γ k) : Set j where
  constructor mkTm
  field
    ᴬ  : (γ : Con.ᴬ Γ) → Ty.ᴬ A γ
    ᴹ  : ∀ {γ₀ γ₁}(γᴹ : Con.ᴹ Γ γ₀ γ₁) → Ty.ᴹ A γᴹ (ᴬ γ₀) (ᴬ γ₁)
    ᴾ  : Tmᴾ {Γ}{k} A
    ᴾᴰ : Tmᴾᴰ {Γ}{k} A ᴾ
    ᴾˢ : Tmᴾˢ {Γ}{k} A ᴾᴰ

record Sub (Γ : Con)(Δ : Con) : Set j where
  constructor mkSub
  field
    ᴬ  : Con.ᴬ Γ → Con.ᴬ Δ
    ᴹ  : {γ₀ γ₁ : Γ .Con.ᴬ}(γᴹ : Γ .ᴹ γ₀ γ₁) → Δ .ᴹ (ᴬ γ₀) (ᴬ γ₁)
    ᴾ  : Γ .ᴾ → Δ .ᴾ
    ᴾᴰ : (γ : Γ .Con.ᴾ) → Γ .ᴾᴰ γ → Δ .ᴾᴰ (ᴾ γ)
    ᴾˢ : (γ : Γ .Con.ᴾ)(γᴾᴰ : Γ .Con.ᴾᴰ γ) → Γ .Con.ᴾˢ γ γᴾᴰ
         → Δ .ᴾˢ (ᴾ γ) (ᴾᴰ γ γᴾᴰ)
open Sub public

∙ : Con
∙ = mkCon (Lift ⊤) (λ _ _ → Lift ⊤)
          (Lift ⊤) (λ _ → Lift ⊤)
          (λ _ _ → Lift ⊤)

▶ᴾ : ∀{k}(Γ : Con)(A : Ty Γ k) → Set₁
▶ᴾ {P} Γ A = Σ (Γ .ᴾ) (A .ᴾ)
▶ᴾ {S} Γ A = (Γ .ᴾ) × (A .ᴾ)

▶ᴾᴰ : ∀{k}(Γ : Con)(A : Ty Γ k) → ▶ᴾ Γ A → Set₁
▶ᴾᴰ {P} Γ A (γ , α) = Σ (Γ .ᴾᴰ γ) λ γᴾᴰ → A .ᴾᴰ γ γᴾᴰ α
▶ᴾᴰ {S} Γ A (γ , α) = (Γ .ᴾᴰ γ)  × (A .ᴾᴰ α)

▶ᴾˢ : ∀{k}(Γ : Con)(A : Ty Γ k)(γα : ▶ᴾ Γ A) → ▶ᴾᴰ Γ A γα → Set
▶ᴾˢ {P} Γ A (γ , α) (γᴾᴰ , αᴾᴰ) =
  Σ (Γ .ᴾˢ γ γᴾᴰ) λ γᴾˢ → A .ᴾˢ γᴾᴰ γᴾˢ α αᴾᴰ
▶ᴾˢ {S} Γ A (γ , α) (γᴾᴰ , αᴾᴰ) =
  Γ .ᴾˢ γ γᴾᴰ × A .ᴾˢ α αᴾᴰ

_▶_ : ∀{k}(Γ : Con) → Ty Γ k → Con
Γ ▶ A = mkCon
  (Σ (Γ .ᴬ) (A .ᴬ))
  (λ γ₀ γ₁ → Σ (Γ .ᴹ (₁ γ₀) (₁ γ₁)) λ γᴹ → A .ᴹ γᴹ (₂ γ₀) (₂ γ₁))
  (▶ᴾ Γ A)
  (▶ᴾᴰ Γ A)
  (▶ᴾˢ Γ A)

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} {Γ} {Δ} A σ =
  mkTy
    (λ γ → ᴬ A (ᴬ σ γ))
    (λ {γ₀}{γ₁} γᴹ α₀ α₁ → A .ᴹ (σ .ᴹ γᴹ) α₀ α₁)
    (λ γ → A .ᴾ (σ .ᴾ γ))
    (λ γ γᴾᴰ α → A .ᴾᴰ (σ .ᴾ γ) (σ .ᴾᴰ γ γᴾᴰ) α )
    (λ {γᴾ} γᴾᴰ γᴾˢ α αᴾᴰ → A .ᴾˢ (σ .ᴾᴰ γᴾ γᴾᴰ) (σ .ᴾˢ γᴾ γᴾᴰ γᴾˢ) α αᴾᴰ)
_[_]T {S} {Γ} {Δ} A σ =
  mkTy
    (λ γ → A .ᴬ (σ .ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ α₀ α₁ → A .ᴹ (σ .ᴹ γᴹ) α₀ α₁)
    (A .ᴾ)
    (A .ᴾᴰ)
    (A .ᴾˢ)

id : ∀{Γ} → Sub Γ Γ
id {Γ} =
  mkSub
    (λ γ → γ)
    (λ γᴹ → γᴹ)
    (λ γ → γ)
    (λ _ γᴾᴰ → γᴾᴰ)
    (λ _ _ γᴾˢ → γᴾˢ)

_∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
_∘_ {Γ}{Δ}{Σ} σ δ =
  mkSub
    (λ γ → σ .ᴬ (δ .ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ (δ .ᴹ γᴹ))
    (λ x → σ .ᴾ (δ .ᴾ x))
    (λ γ γᴾᴰ → σ .ᴾᴰ (δ .ᴾ γ) (δ .ᴾᴰ γ γᴾᴰ))
    (λ γ γᴾᴰ γᴾˢ → σ .ᴾˢ (δ .ᴾ γ) (δ .ᴾᴰ γ γᴾᴰ) (δ .ᴾˢ γ γᴾᴰ γᴾˢ))

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = _  -- inferable by ⊤ η

_,s_  : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,s_ {P} {Γ} {Δ} σ {A} t =
  mkSub
    (λ γ → (σ .ᴬ γ) , t .Tm.ᴬ γ)
    (λ {γ₀}{γ₁} γᴹ → (ᴹ σ γᴹ) , (t .Tm.ᴹ γᴹ))
    (λ γ → (ᴾ σ γ) , (t .Tm.ᴾ γ))
    (λ γ γᴾᴰ → (ᴾᴰ σ γ γᴾᴰ) , (t .Tm.ᴾᴰ γ γᴾᴰ))
    (λ γ γᴾᴰ γᴾˢ → (ᴾˢ σ γ γᴾᴰ γᴾˢ) , t .Tm.ᴾˢ γ γᴾᴰ γᴾˢ)
_,s_ {S} {Γ} {Δ} σ {A} t =
  mkSub
    (λ γ → (σ .ᴬ γ) , t .Tm.ᴬ γ)
    (λ {γ₀}{γ₁} γᴹ → (ᴹ σ γᴹ) , (t .Tm.ᴹ γᴹ))
    (λ γ → (ᴾ σ γ) , (t .Tm.ᴾ γ))
    (λ γ γᴾᴰ → (ᴾᴰ σ γ γᴾᴰ) , (t .Tm.ᴾᴰ γ γᴾᴰ))
    (λ γ γᴾᴰ γᴾˢ → (ᴾˢ σ γ γᴾᴰ γᴾˢ) , t .Tm.ᴾˢ γ γᴾᴰ γᴾˢ)

π₁    : ∀{k Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P} {Γ} {Δ} {A} σ =
  mkSub
    (λ γ → σ .ᴬ γ .₁)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₁)
    (λ γ → σ .ᴾ γ .₁ )
    (λ γ γᴾᴰ → σ .ᴾᴰ γ γᴾᴰ .₁)
    (λ γ γᴾᴰ γᴾˢ → σ .ᴾˢ γ γᴾᴰ γᴾˢ .₁)
π₁ {S} {Γ} {Δ} {A} σ =
  mkSub
    (λ γ → σ .ᴬ γ .₁)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₁)
    (λ γ → σ .ᴾ γ .₁ )
    (λ γ γᴾᴰ → σ .ᴾᴰ γ γᴾᴰ .₁)
    (λ γ γᴾᴰ γᴾˢ → σ .ᴾˢ γ γᴾᴰ γᴾˢ .₁)

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} {Γ} {Δ} {A} t σ =
  mkTm
    (λ γ → t .Tm.ᴬ (σ .ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → t .Tm.ᴹ (σ .ᴹ γᴹ))
    (λ γ → t .Tm.ᴾ (σ .ᴾ γ))
    (λ γ γᴾᴰ → t .Tm.ᴾᴰ (σ .ᴾ γ) (σ .ᴾᴰ γ γᴾᴰ))
    (λ γ γᴾᴰ γᴾˢ → t .Tm.ᴾˢ (σ .ᴾ γ) (σ .ᴾᴰ γ γᴾᴰ) (σ .ᴾˢ γ γᴾᴰ γᴾˢ))
_[_]t {S} {Γ} {Δ} {A} t σ =
  mkTm
    (λ γ → t .Tm.ᴬ (σ .ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ → t .Tm.ᴹ (σ .ᴹ γᴹ))
    (λ γ → t .Tm.ᴾ (σ .ᴾ γ))
    (λ γ γᴾᴰ → t .Tm.ᴾᴰ (σ .ᴾ γ) (σ .ᴾᴰ γ γᴾᴰ))
    (λ γ γᴾᴰ γᴾˢ → t .Tm.ᴾˢ (σ .ᴾ γ) (σ .ᴾᴰ γ γᴾᴰ) (σ .ᴾˢ γ γᴾᴰ γᴾˢ))

π₂ : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)
π₂ {P} {Γ} {Δ} {A} σ =
  mkTm
    (λ γ → σ .ᴬ γ .₂)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₂)
    (λ γ → σ .ᴾ γ .₂ )
    (λ γ γᴾᴰ → σ .ᴾᴰ γ γᴾᴰ .₂)
    (λ γ γᴾᴰ γᴾˢ → σ .ᴾˢ γ γᴾᴰ γᴾˢ .₂)
π₂ {S} {Γ} {Δ} {A} σ =
  mkTm
    (λ γ → σ .ᴬ γ .₂)
    (λ {γ₀}{γ₁} γᴹ → σ .ᴹ γᴹ .₂)
    (λ γ → σ .ᴾ γ .₂ )
    (λ γ γᴾᴰ → σ .ᴾᴰ γ γᴾᴰ .₂)
    (λ γ γᴾᴰ γᴾˢ → σ .ᴾˢ γ γᴾᴰ γᴾˢ .₂)

[id]T : ∀{k Γ}{A : Ty Γ k} → A [ id ]T ≡ A
[id]T {P} = refl
[id]T {S} = refl

[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
        → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
[][]T {P} = refl
[][]T {S} = refl

idl : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idl = refl

idr : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
idr = refl

ass : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

,∘ : ∀{k Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ k}{t : Tm Γ (A [ δ ]T)}
      → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
,∘ {P} = refl
,∘ {S} = refl

π₁β : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → (π₁ (σ ,s t)) ≡ σ
π₁β {P} = refl
π₁β {S} = refl

πη : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)}
      → (π₁ σ ,s π₂ σ) ≡ σ
πη {P} = refl
πη {S} = refl

εη : ∀{Γ}{σ : Sub Γ ∙}
      → σ ≡ ε
εη = refl

π₂β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
      → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t
π₂β {P} = refl
π₂β {S} = refl

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

vs : ∀{k Γ}{A B : Ty Γ k} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs x = x [ wk ]t

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ S
U {Γ} =
  mkTy
    (λ _ → Set)
    (λ _ A B → (A → B))
    Set
    (λ A → (A → Set))
    (λ A Aᴾᴰ → (α : A) → Aᴾᴰ α)

U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
U[] {Γ}{Δ}{σ} = refl

El : ∀{Γ}(a : Tm Γ U) → Ty Γ P
El {Γ} a =
  mkTy
    (λ γ → Lift (a .Tm.ᴬ γ))
    (λ {γ₀}{γ₁} γᴹ α αᴹ → a .Tm.ᴹ γᴹ (α .lower) ≡ αᴹ .lower)
    (λ γ → Lift (a .Tm.ᴾ γ))
    (λ γ γᴾᴰ α → Lift (a .Tm.ᴾᴰ _ γᴾᴰ (α .lower)))
    (λ {γᴾ} γᴾᴰ γᴾˢ α αᴾᴰ → a .Tm.ᴾˢ _ _ γᴾˢ (α .lower) ≡ αᴾᴰ .lower)

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (coe (Tm Γ & (U[] {σ = σ})) (a [ σ ]t)))
El[] = refl

-- Inductive functions
--------------------------------------------------------------------------------

Π : ∀{k Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} {Γ} a B =
  mkTy
    (λ γ → (x : a .Tm.ᴬ γ) → B .ᴬ (γ , lift x))
    (λ {γ₀}{γ₁} γᴹ f₀ f₁ → (x : a .Tm.ᴬ γ₀)
       → B .ᴹ (γᴹ , refl) (f₀ x) (f₁ (a .Tm.ᴹ γᴹ x)))
    ((λ γ → (x : a .Tm.ᴾ γ) → B .ᴾ (γ , lift x)))
    (λ γ γᴾᴰ f → (x : a .Tm.ᴾ γ)(xᴾᴰ : a .Tm.ᴾᴰ γ γᴾᴰ x)
               → B .ᴾᴰ _ (γᴾᴰ , lift xᴾᴰ) (f x))
    (λ {γ} γᴾᴰ γᴾˢ f fᴾᴰ →
      (x : a .Tm.ᴾ γ)
      → B .ᴾˢ (γᴾᴰ , lift (a .Tm.ᴾˢ γ γᴾᴰ γᴾˢ x))
              (γᴾˢ , refl)
              (f x)
              (fᴾᴰ x (a .Tm.ᴾˢ γ γᴾᴰ γᴾˢ x)))

Π {S} {Γ} a B =
  mkTy
    (λ γ → (x : a .Tm.ᴬ γ) → B .ᴬ (γ , lift x))
    (λ {γ₀}{γ₁} γᴹ f₀ f₁ → (x : a .Tm.ᴬ γ₀)
       → B .ᴹ (γᴹ , refl) (f₀ x) (f₁ (a .Tm.ᴹ γᴹ x)))
    (B .ᴾ)
    (B .ᴾᴰ)
    (B .ᴾˢ)

Π[] :
  {k : PS} {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ {S} (U {Δ})} {B : Ty
  (_▶_ {P} Δ (El {Δ} a)) k} → _≡_ {i} {Ty Γ k} (_[_]T {k} {Γ}
  {Δ} (Π {k} {Δ} a B) σ) (Π {k} {Γ} (tr {i} {j} {Ty Γ S} (Tm Γ
  {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})
  (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)) (tr {i} {i} {Ty Γ P} (λ x →
  Ty (_▶_ {P} Γ x) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ}
  (tr {i} {j} {Ty Γ S} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ}
  {U {Γ}} (U[] {Γ} {Δ} {σ}) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))}
  (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ}
  {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ
  (El {Δ} a)))))
Π[] {P} = refl
Π[] {S} = refl

app : ∀{k Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a) k} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app {P} {Γ} {a} {B} t =
  mkTm
    (λ {(γ , α) → t .Tm.ᴬ γ (α .lower)})
    (λ { {γ₀ , α₀}{γ₁ , α₁}(γᴹ , αᴹ) →
       J (λ x p → ᴹ B (γᴹ , p) (t .Tm.ᴬ γ₀ (α₀ .lower)) (t .Tm.ᴬ γ₁ x))
         (t .Tm.ᴹ γᴹ (α₀ .lower))
         αᴹ})
    (λ {(γ , α) → t .Tm.ᴾ γ (α .lower)})
    (λ { (γ , α) (γᴾᴰ , αᴾᴰ) → t .Tm.ᴾᴰ γ γᴾᴰ (α .lower) (αᴾᴰ .lower)})
    (λ {(γ , lift α) (γᴾᴰ , lift αᴾᴰ) (γᴾˢ , αᴾˢ) →
       J (λ αᴾᴰ αᴾˢ → B .ᴾˢ (γᴾᴰ , lift αᴾᴰ) (γᴾˢ , αᴾˢ) (t .Tm.ᴾ γ α)
          (t .Tm.ᴾᴰ γ γᴾᴰ α αᴾᴰ)) (t .Tm.ᴾˢ γ γᴾᴰ γᴾˢ α) αᴾˢ})

app {S} {Γ} {a} {B} t =
  mkTm
    (λ {(γ , α) → t .Tm.ᴬ γ (α .lower)})
    (λ { {γ₀ , α₀}{γ₁ , α₁}(γᴹ , αᴹ) →
       J (λ x p → ᴹ B (γᴹ , p) (t .Tm.ᴬ γ₀ (α₀ .lower)) (t .Tm.ᴬ γ₁ x))
         (t .Tm.ᴹ γᴹ (α₀ .lower))
         αᴹ})
    (λ {(γ , α) → t .Tm.ᴾ γ})
    (λ {(γ , α) (γᴾᴰ , αᴾᴰ) → t .Tm.ᴾᴰ γ γᴾᴰ})
    λ {(γ , α) (γᴾᴰ , αᴾᴰ) (γᴾˢ , αᴾˢ) → t .Tm.ᴾˢ γ γᴾᴰ γᴾˢ}

app[] :
     {k : PS} {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ {S} (U {Δ})} {B : Ty (_▶_
     {P} Δ (El {Δ} a)) k} {t : Tm Δ {k} (Π {k} {Δ} a B)} → _≡_ {j} {Tm (_▶_
     {P} Γ (El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ
     {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U
     {Δ}} a σ)))) {k} (tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_ {P} Γ z) k)
     {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set
     j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
     (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k}
     {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B
     (_^_ {P} {Γ} {Δ} σ (El {Δ} a))))} (tr2 {i} {i} {j} {Ty Γ P} {λ z → Ty
     (_▶_ {P} Γ z) k} (λ A → Tm (_▶_ {P} Γ A) {k}) {_[_]T {P} {Γ} {Δ} (El
     {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)}
     {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T
     {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ}
     {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) {_[_]T {k} {_▶_ {P} Γ (_[_]T {P}
     {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El
     {Δ} a))} {tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_ {P} Γ z) k) {_[_]T {P}
     {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U
     {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set j} (Tm Γ
     {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t
     {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P}
     Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P}
     {Γ} {Δ} σ (El {Δ} a)))} refl (_[_]t {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ}
     (El {Δ} a) σ)} {_▶_ {P} Δ (El {Δ} a)} {B} (app {k} {Δ} {a} {B} t) (_^_
     {P} {Γ} {Δ} σ (El {Δ} a)))) (app {k} {Γ} {coe {j} {Tm Γ {S} (_[_]T {S}
     {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j} {Ty Γ S} {Set
     j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
     (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)} {tr {i} {i} {Ty Γ P} (λ z → Ty (_▶_
     {P} Γ z) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {j} {Tm Γ
     {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j}
     {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[]
     {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a})
     (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)} {_▶_ {P} Δ (El
     {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El {Δ} a)))} (tr {i} {j} {Ty Γ k} (Tm Γ
     {k}) {_[_]T {k} {Γ} {Δ} (Π {k} {Δ} a B) σ} {Π {k} {Γ} (coe {j} {Tm Γ
     {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_ {i} {suc j}
     {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[]
     {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ)) (tr {i} {i} {Ty Γ P} (λ
     z → Ty (_▶_ {P} Γ z) k) {_[_]T {P} {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe
     {j} {Tm Γ {S} (_[_]T {S} {Γ} {Δ} (U {Δ}) σ)} {Tm Γ {S} (U {Γ})} (_&_
     {i} {suc j} {Ty Γ S} {Set j} (Tm Γ {S}) {_[_]T {S} {Γ} {Δ} (U {Δ}) σ}
     {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {S} {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ}
     {Δ} {σ} {a}) (_[_]T {k} {_▶_ {P} Γ (_[_]T {P} {Γ} {Δ} (El {Δ} a) σ)}
     {_▶_ {P} Δ (El {Δ} a)} B (_^_ {P} {Γ} {Δ} σ (El {Δ} a))))} (Π[] {k}
     {Γ} {Δ} {σ} {a} {B}) (_[_]t {k} {Γ} {Δ} {Π {k} {Δ} a B} t σ)))
app[] {P} = refl
app[] {S} = refl
