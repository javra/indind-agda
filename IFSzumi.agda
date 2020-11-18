module IFSzumi where

open import Lib
open import IF
open import IFA

CodS : TyS → TyP (∙c ▶c U)
CodS U        = El vz
CodS (T ⇒̂S B) = Π̂P T λ _ → CodS B

CodC : SCon → Con (∙c ▶c U)
CodC ∙c        = ∙
CodC (Γc ▶c B) = CodC Γc ▶P CodS B

Codt : ∀{Γc υc B}(υ : _ᵃC {zero} (CodC Γc) (_ , υc)) → Tm Γc B → TmP (CodC Γc) (CodS B)
Codt υ       (var vvz)     = vzP
Codt (υ , _) (var (vvs x)) = vsP (Codt υ (var x))
Codt υ       (t $S τ)      = Codt υ t $̂P τ

module El {Γc : SCon} {υc : Set} (υ : _ᵃC {zero} (CodC Γc) (_ , υc)) where

  ElP : TyP Γc → TyP (∙c ▶c υc ⇒̂S U)
  ElP (El a)   = El (vz $S (Codt υ a ᵃtP) υ)
  ElP (Π̂P T A) = Π̂P T λ τ → ElP (A τ)
  ElP (a ⇒P A) = (vz $S (Codt υ a ᵃtP) υ) ⇒P ElP A

  ElC : Con Γc → Con (∙c ▶c υc ⇒̂S U)
  ElC ∙        = ∙
  ElC (Γ ▶P A) = ElC Γ ▶P ElP A

-- Functor from algebras to Szumified algebras
F0c : (Γc : SCon) → Set
F0c ∙c        = ⊤
F0c (Γc ▶c B) = F0c Γc ⊎ ⊤

F0t : ∀{Γc B} → Tm Γc B → F0c Γc
F0t (var vvz)     = inr _
F0t (var (vvs v)) = inl (F0t (var v))
F0t (t $S τ)      = F0t t

F0P : ∀{υc}(α : υc)(B : TyS) → _ᵃP {zero} (CodS B) (_ , υc)
F0P α U        = α
F0P α (T ⇒̂S B) = λ _ → F0P α B

F0C' : ∀{Ωc Γc : SCon}(σ : Sub Ωc Γc) → _ᵃC {zero} (CodC Γc) (_ , F0c Ωc)
F0C'               ε       = _
F0C' {Ωc}{Γc ▶c B} (σ , t) = F0C' σ , F0P (F0t t) B

F0C : ∀{Γc} → _ᵃC {zero} (CodC Γc) (_ , F0c Γc)
F0C {Γc} = F0C' {Γc} IF.id

-- Functor from Szumified algebras to original algebras
GS : ∀ B {υc}(α : _ᵃP {zero} (CodS B) (_ , υc)) → _ᵃS {zero} B
GS U α = {!!}
GS (T ⇒̂S B) α = λ τ → GS B {!!}

Gc : ∀{Γc}{υc}(υ : _ᵃC {zero} (CodC Γc) (_ , υc)) → _ᵃc {zero} Γc
Gc {∙c}      υ       = _
Gc {Γc ▶c B} (υ , α) = Gc υ , {!!}

  



