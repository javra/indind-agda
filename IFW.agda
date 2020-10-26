{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFD
open import IFE

module IFW {ℓ}{Ωc}(Ω : Con Ωc)
  {ωc : _ᵃc {ℓ} (ᴱc Ωc)}(ω : (ᴱC Ω ᵃC) ωc) where

ʷS' : ∀{ℓ} → TyS → Set ℓ → Set ℓ
ʷS' U        X = X
ʷS' (T ⇒̂S B) X = T → ʷS' B X

ʷc : ∀{Γc}(σ : Sub Ωc Γc) → ᵈc {suc ℓ} (ᴱc Γc) ((ᴱs σ ᵃs) ωc)
ʷc ε                 = lift tt
ʷc (_,_ {B = B} σ t) = ʷc σ , λ _ → ʷS' B (Set ℓ)

ʷ²S : TyS → Set (suc ℓ)
ʷ²S U        = Set _
ʷ²S (T ⇒̂S B) = T → T → ʷ²S B

unc : (B : TyS)(Acc : Set) → Set
unc U        Acc = Acc
unc (T ⇒̂S B) Acc = T × unc B Acc

f1 : (B : TyS) → ʷ²S B → unc B ⊤ → unc B ⊤ → Set ℓ
f1 U        w l       k        = w
f1 (T ⇒̂S B) w (τ , l) (τ' , k) = f1 B (w τ τ') l k

cur : ∀{ℓ}(B : TyS)(X : Set ℓ) → (unc B ⊤ → X) → ʷS' B X
cur U        X f = f tt
cur (T ⇒̂S B) X f = λ τ → cur B X λ l → f (τ , l)

f2 : (B : TyS) → (unc B ⊤ → unc B ⊤ → Set ℓ) → ʷS' B (ʷS' B (Set ℓ))
f2 B f = cur B (ʷS' B (Set ℓ)) λ l → cur B (Set ℓ) (f l)

ʷv' : (B : TyS) (A : Set ℓ) → ʷ²S B
ʷv' U        A = A
ʷv' (T ⇒̂S B) A = λ τ τ' → ʷv' B (A × (τ ≡ τ'))

ʷv : (B : TyS) → ʷS' B (ʷS' B (Set ℓ))
ʷv B = f2 B (f1 B (ʷv' B (Lift _ ⊤)))

hd : ∀{B}{Γc}(t : Tm Γc B) → TyS
hd {B} (var x)  = B
hd     (t $S x) = hd t

ʷt' : ∀{B}{Γc}(t : Tm Γc B) → ʷS' B (ʷS' (hd t) (Set ℓ))
ʷt' {B} (var x)  = ʷv B
ʷt'     (t $S τ) = ʷt' t τ

ʷt= : ∀{B}{Γc}(σ : Sub Ωc Γc)(t : Tm Γc B)(α : (ᴱt t ᵃt) ((ᴱs σ ᵃs) ωc)) → ᵈt (ᴱt t) (ʷc σ) α ≡ ʷS' (hd t) (Set ℓ)
ʷt= (σ , s) (var vvz)     α = refl
ʷt= (σ , s) (var (vvs v)) α = ʷt= σ (var v) α
ʷt= ε       (t $S τ)      α = ʷt= ε t α
ʷt= (σ , s) (t $S τ)      α = ʷt= (σ , s) t α

ʷt=id : ∀{B}(t : Tm Ωc B)(α : (ᴱt t ᵃt) ωc) → ᵈt (ᴱt t) (ʷc id) α ≡ ʷS' (hd t) (Set ℓ)
ʷt=id t α = ʷt= id t α
{-# REWRITE ʷt=id #-}

ʷP : ∀ A (α : (ᴱP A ᵃP) ωc) → ᵈP (ᴱP A) (ʷc id) α
ʷP (El a)   α = ʷt' a
ʷP (Π̂P T A) ϕ = λ τ → ʷP (A τ) (ϕ τ)
ʷP (a ⇒P A) ϕ = λ α αᵈ → ʷP A (ϕ α)

ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC (ᴱC Γ) (ʷc id) ((ᴱsP σP ᵃsP) ω)
ʷC εP                   = lift tt
ʷC (_,P_ {A = A} σP tP) = ʷC σP , ʷP A ((ᴱtP tP ᵃtP) ω)
