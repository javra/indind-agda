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
-- F0 is the code part, F1 is the element part of the result
F0S : TyS → Set
F0S U        = ⊤
F0S (T ⇒̂S B) = T × F0S B

F0c : (Γc : SCon) → Set
F0c ∙c        = ⊤
F0c (Γc ▶c B) = F0c Γc ⊎ F0S B

hd : ∀{Γc B}(t : Tm Γc B) → TyS
hd {B = B} (var v) = B
hd        (t $S τ) = hd t 

F0S' : (Γc : SCon)(B : TyS) → Set
F0S' Γc U = F0c Γc
F0S' Γc (T ⇒̂S B) = T → F0S' Γc B

F0S'fun : ∀{Γc Γc'}(B : TyS)(f : F0c Γc → F0c Γc')
          →  F0S' Γc B → F0S' Γc' B
F0S'fun U        f γ = f γ
F0S'fun (T ⇒̂S B) f γ = λ τ → F0S'fun B f (γ τ)

F0t : ∀{Γc B}(t : Tm Γc B) → F0S' Γc B
F0t {B = U}      (var vvz) = inr _
F0t {B = T ⇒̂S B} (var vvz) = λ τ → F0S'fun B (λ { (inl x) → inl x ;
                                                  (inr x) → inr (τ , x) }) (F0t {B = B} (var vvz))
F0t {B = B}      (var (vvs x)) = F0S'fun B inl (F0t (var x))
F0t              (t $S τ)      = F0t t τ

F0P : ∀{Ωc B}(t : Tm Ωc B) → (CodS B ᵃP) (_ , F0c Ωc)
F0P {B = U} t = F0t t
F0P {B = T ⇒̂S B} t = λ τ → F0P {B = B} (t $S τ)

F0C' : ∀{Ωc Γc}(σ : Sub Ωc Γc) → _ᵃC {zero} (CodC Γc) (_ , F0c Ωc)
F0C' ε       = _
F0C' (σ , t) = F0C' σ , F0P t

F0C : ∀{Γc} → _ᵃC {zero} (CodC Γc) (_ , F0c Γc)
F0C {Γc} = F0C' {Γc} IF.id

F1S : ∀{B}(α : _ᵃS {zero} B) → Set
F1S {U}      α = α
F1S {T ⇒̂S B} α = F1S {B} (α {!!})

F1c : ∀{Γc}(γc : _ᵃc {zero} Γc) → F0c Γc → Set
F1c {∙c}      γc       _        = ⊤
F1c {Γc ▶c B} (γc , α) (inl υc) = F1c {Γc} γc υc
F1c {Γc ▶c B} (γc , α) (inr _)  = F1S {B} α

module F1 {Γc : SCon}{γc : _ᵃc {zero} Γc} where
  open El {Γc}{F0c Γc}(F0C {Γc})

  F1C : (Γ : Con Γc) → _ᵃC {zero} (ElC Γ) (_ , F1c γc)
  F1C Γ = {!!}

-- Functor from Szumified algebras to original algebras
GS : ∀ B {υc}(α : _ᵃP {zero} (CodS B) (_ , υc)) → _ᵃS {zero} B
GS U α = {!!}
GS (T ⇒̂S B) α = λ τ → GS B {!!}

Gc : ∀{Γc}{υc}(υ : _ᵃC {zero} (CodC Γc) (_ , υc)) → _ᵃc {zero} Γc
Gc {∙c}      υ       = _
Gc {Γc ▶c B} (υ , α) = Gc υ , {!!}

  



