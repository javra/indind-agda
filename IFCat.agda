module IFCat where

open import Lib hiding (id; _∘_)
open import IF
open import IFA
open import IFM

idᵐS : ∀{ℓ B}(α : _ᵃS {ℓ} B) → ᵐS B α α
idᵐS {B = U}      α = λ x → x
idᵐS {B = Π̂S T x} α = λ τ → idᵐS (α τ)

idᵐc : ∀{ℓ Γc}(γc : _ᵃc {ℓ} Γc) → ᵐc Γc γc γc
idᵐc {Γc = ∙c}      γc       = lift tt
idᵐc {Γc = Γc ▶c B} (γc , α) = idᵐc γc , idᵐS α

idᵐt : ∀{ℓ Γc B}(t : Tm Γc B)(γc : _ᵃc {ℓ} Γc) → ᵐt t (idᵐc γc) ≡ idᵐS ((t ᵃt) γc)
idᵐt (var vvz)     γc       = refl
idᵐt (var (vvs t)) (γc , α) = idᵐt (var t) γc
idᵐt (f $S τ)      γc       = happly (idᵐt f γc) τ

idᵐP : ∀{ℓ Γc A}{γc : _ᵃc {ℓ} Γc}(α : _ᵃP {ℓ} A γc) → ᵐP A (idᵐc γc) α α
idᵐP {A = El a}   α = lift (happly (idᵐt a _) α)
idᵐP {A = Π̂P T B} α = λ τ → idᵐP (α τ)
idᵐP {A = a ⇒P A} α = λ x → coe (ᵐP A (idᵐc _) (α x) & (α & happly (idᵐt a _ ⁻¹) x))
                              (idᵐP {A = A} (α x))

idᵐC : ∀{ℓ Γc Γ}{γc : _ᵃc {ℓ} Γc}(γ : _ᵃC {ℓ} Γ γc) → ᵐC Γ (idᵐc γc) γ γ
idᵐC {Γ = ∙}      γ       = lift tt
idᵐC {Γ = Γ ▶P A} (γ , α) = idᵐC γ , idᵐP α
