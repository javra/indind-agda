module IFSzumi where

open import Lib
open import IF
open import IFA

SUEl : SCon
SUEl = ∙c ▶c U ▶c {!!}

CodS : TyS → TyP (∙c ▶c U)
CodS U        = El vz
CodS (Π̂S T B) = Π̂P T λ τ → CodS (B τ)

Codc : SCon → Con (∙c ▶c U)
Codc ∙c        = ∙
Codc (Γc ▶c B) = Codc Γc ▶P CodS B

Elt : ∀{Γc υc B}(υ : _ᵃC {zero} (Codc Γc) (lift tt , υc)) → Tm Γc B → TmP (Codc Γc) (CodS B)
Elt υ       (var vvz)     = vzP
Elt (υ , _) (var (vvs x)) = vsP (Elt υ (var x))
Elt υ       (t $S τ)      = Elt υ t $̂P τ

module El {Γc : SCon} {υc : Set} (υ : _ᵃC {zero} (Codc Γc) (lift tt , υc)) where

  ElP : TyP Γc → TyP (∙c ▶c Π̂S υc (λ _ → U))
  ElP (El a)   = El (vz $S (Elt υ a ᵃtP) υ)
  ElP (Π̂P T A) = Π̂P T λ τ → ElP (A τ)
  ElP (a ⇒P A) = (vz $S (Elt υ a ᵃtP) υ) ⇒P ElP A

  ElC : Con Γc → Con (∙c ▶c (Π̂S υc (λ _ → U)))
  ElC ∙        = ∙
  ElC (Γ ▶P A) = ElC Γ ▶P ElP A

