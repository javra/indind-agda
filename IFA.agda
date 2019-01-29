module IFA where

open import Lib hiding (id; _∘_)
open import IFSyntax

_ᴬS : TyS → Set₁
U ᴬS = Set
Π̂S T A ᴬS = (α : T) → (A α) ᴬS

_ᴬc : SCon → Set₁
∙c ᴬc = Lift ⊤
(Γ ▶c A) ᴬc = Γ ᴬc × A ᴬS

_ᴬt : {Γ : SCon}{A : TyS} → Tm Γ A → Γ ᴬc → A ᴬS
(vz ᴬt) (γ , α) = α
(vs t ᴬt) (γ , α) = (t ᴬt) γ
((t $S α) ᴬt) γ = (t ᴬt) γ α

_ᴬP : {ΓT : SCon} → TyP ΓT → (γ : ΓT ᴬc) → Set₁
(Π̂P T A ᴬP) γ = (α : T) → ((A α) ᴬP) γ
(El a ᴬP) γ = Lift ((a ᴬt) γ)
((a ⇒P B) ᴬP) γ = (a ᴬt) γ → (B ᴬP) γ

_ᴬC : {ΓT : SCon} → Con ΓT → ΓT ᴬc → Set₁
(∙ ᴬC) γ = Lift ⊤
((Γ ▶S A) ᴬC) (γ , _) = (Γ ᴬC) γ × A ᴬS
((Γ ▶P A) ᴬC) γ = (Γ ᴬC) γ × (A ᴬP) γ
