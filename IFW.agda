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

f1 : {B : TyS} → ʷ²S B → unc B ⊤ → unc B ⊤ → Set ℓ
f1 {U}      w l       k        = w
f1 {T ⇒̂S B} w (τ , l) (τ' , k) = f1 (w τ τ') l k

cur : ∀{ℓ}(B : TyS)(X : Set ℓ) → (unc B ⊤ → X) → ʷS' B X
cur U        X f = f tt
cur (T ⇒̂S B) X f = λ τ → cur B X λ l → f (τ , l)

f2 : {B : TyS} → (unc B ⊤ → unc B ⊤ → Set ℓ) → ʷS' B (ʷS' B (Set ℓ))
f2 {B} f = cur B (ʷS' B (Set ℓ)) λ l → cur B (Set ℓ) (f l)

ʷv' : (B : TyS) (A : Set ℓ) → ʷ²S B
ʷv' U        A = A
ʷv' (T ⇒̂S B) A = λ τ τ' → ʷv' B (A × (τ ≡ τ'))

hd : ∀{B}{Γc}(t : Tm Γc B) → TyS
hd {B} (var x)  = B
hd     (t $S τ) = hd t

hdfill : ∀{B}(t : Tm Ωc B){X : Set (suc ℓ)} → ʷS' (hd t) X → ʷS' B X
hdfill (var x)  α = α
hdfill (t $S τ) α = hdfill t α τ

ʷt= : ∀{B}{Γc}(σ : Sub Ωc Γc)(t : Tm Γc B)(α : (ᴱt t ᵃt) ((ᴱs σ ᵃs) ωc)) → ᵈt (ᴱt t) (ʷc σ) α ≡ ʷS' (hd t) (Set ℓ)
ʷt= (σ , s) (var vvz)     α = refl
ʷt= (σ , s) (var (vvs v)) α = ʷt= σ (var v) α
ʷt= ε       (t $S τ)      α = ʷt= ε t α
ʷt= (σ , s) (t $S τ)      α = ʷt= (σ , s) t α

ʷt=idv : ∀{B}(v : Var Ωc B)(α : (var (ᴱv v) ᵃt) ωc) → ᵈt (var (ᴱv v)) (ʷc id) α ≡ ʷS' B (Set ℓ)
ʷt=idv v α = ʷt= id (var v) α
{-# REWRITE ʷt=idv #-}

ʷt=id : ∀{B}(t : Tm Ωc B)(α : (ᴱt t ᵃt) ωc) → ᵈt (ᴱt t) (ʷc id) α ≡ ʷS' (hd t) (Set ℓ)
ʷt=id t α = ʷt= id t α
{-# REWRITE ʷt=id #-}

ʷP : ∀ A (α : (ᴱP A ᵃP) ωc)(X : Set ℓ) → ᵈP (ᴱP A) (ʷc id) α
ʷP (El a)   α X = hdfill a (f2 (f1 (ʷv' (hd a) X))) -- check again, maybe revive old ʷt'
ʷP (Π̂P T A) ϕ X = λ τ → ʷP (A τ) (ϕ τ) X
ʷP (a ⇒P A) ϕ X = λ α αᵈ → ʷP A (ϕ α) (X × hdfill a αᵈ)

ʷC : ∀{Γ}(σP : SubP Ω Γ) → ᵈC (ᴱC Γ) (ʷc id) ((ᴱsP σP ᵃsP) ω)
ʷC εP                   = lift tt
ʷC (_,P_ {A = A} σP tP) = ʷC σP , ʷP A ((ᴱtP tP ᵃtP) ω) (Lift _ ⊤)
