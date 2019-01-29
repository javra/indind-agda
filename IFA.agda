module IFA where

open import Lib hiding (id; _∘_)
open import IFSyntax

_ᴬS : TyS → Set₁
U ᴬS = Set
Π̂S T A ᴬS = (α : T) → (A α) ᴬS

_ᴬT : TCon → Set₁
∙t ᴬT = Lift ⊤
(Γ ▶t A) ᴬT = Γ ᴬT × A ᴬS

_ᴬt : {Γ : TCon}{A : TyS} → Tm Γ A → Γ ᴬT → A ᴬS
(vz ᴬt) (γ , α) = α
(vs t ᴬt) (γ , α) = (t ᴬt) γ
((t $S α) ᴬt) γ = (t ᴬt) γ α

_ᴬP : {ΓT : TCon} → TyP ΓT → (γ : ΓT ᴬT) → Set₁
(Π̂P T A ᴬP) γ = (α : T) → ((A α) ᴬP) γ
(El a ᴬP) γ = Lift ((a ᴬt) γ)
((a ⇒P B) ᴬP) γ = (a ᴬt) γ → (B ᴬP) γ

_ᴬC : {ΓT : TCon} → Con ΓT → ΓT ᴬT → Set₁
(∙ ᴬC) γ = Lift ⊤
((Γ ▶S A) ᴬC) (γ , _) = (Γ ᴬC) γ × A ᴬS
((Γ ▶P A) ᴬC) γ = (Γ ᴬC) γ × (A ᴬP) γ
