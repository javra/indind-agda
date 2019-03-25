module II where

open import Lib hiding (id; _∘_)

data PS : Set where P S : PS

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 3 _▶_

postulate
  Con : Set
  Ty  : Con → PS → Set
  Tm  : ∀ Γ → ∀ {k} → Ty Γ k → Set
  Sub : Con → Con → Set

  ∙     : Con
  _▶_   : ∀{k}(Γ : Con) → Ty Γ k → Con

  _[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k

  id    : ∀{Γ} → Sub Γ Γ
  _∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  ε     : ∀{Γ} → Sub Γ ∙
  _,s_  : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  π₁    : ∀{k Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ

  _[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  π₂    : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)

  [id]T : ∀{k Γ}{A : Ty Γ k} → A [ id ]T ≡ A
  [][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T

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

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

vs : ∀{k l Γ}{A : Ty Γ k}{B : Ty Γ l} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs x = x [ wk ]t

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {k}{Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {k}{Γ}{A [ σ ]T})

infixl 5 _^_


-- Universe
--------------------------------------------------------------------------------

postulate
  U    : ∀{Γ} → Ty Γ S
  U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
  El   : ∀{Γ}(a : Tm Γ U) → Ty Γ P
  El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (coe (Tm Γ & U[]) (a [ σ ]t)))

-- Inductive functions
--------------------------------------------------------------------------------
postulate
  Π : ∀{k Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a) k) → Ty Γ k

  Π[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}
      → (Π a B) [ σ ]T ≡ Π (tr (Tm Γ) U[] (a [ σ ]t))
                           (tr (λ x → Ty (Γ ▶ x) k) El[] (B [ σ ^ El a ]T))

  app : ∀{k Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a) k} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B

  app[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))


-- External functions
------------------------------------------------------------------------------
postulate
  Π̂ : ∀{k Γ}(T : Set)(B : T → Ty Γ k) → Ty Γ k
  Π̂[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{T : Set}{B : T → Ty Δ k}
        → (Π̂ T B) [ σ ]T ≡ Π̂ T λ τ → B τ [ σ ]T

  âpp : ∀{k Γ T}{B : T → Ty Γ k}(f : Tm Γ (Π̂ T B))(τ : T) → Tm Γ (B τ)
  âpp[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{T}{B : T → Ty Δ k}{f : Tm Δ (Π̂ T B)}{τ : T}
          → âpp {B = λ τ → B τ [ σ ]T} (tr (Tm Γ) Π̂[] (f [ σ ]t)) τ ≡ (âpp f τ) [ σ ]t
