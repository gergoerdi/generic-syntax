\begin{code}[hide]
open import GenericSyntax.Util

module GenericSyntax.Examples.STLC.Let where

open import GenericSyntax.Examples.STLC.Core using (Ty; Style; Curry; Church; APP; LAM_style; LET)
open import GenericSyntax.Desc Ty
open import GenericSyntax.Ctx Ty
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
open import Data.Product
\end{code}

%<*LANG>
\begin{code}
data Flavour : Set where
  sugared desugared : Flavour

data `STLC : Flavour → Set where
  `app `lam : ∀ {φ} → `STLC φ
  `let : `STLC sugared

STLC : Flavour → Style → Desc
STLC φ s = sg (`STLC φ) λ
  {  `app  → APP
  ;  `lam  → LAM s style
  ;  `let  → LET
  }
\end{code}
%</LANG>

\begin{code}[hide]
open import GenericSyntax.Repr Ty
open Typed using (var; con; sg; node)
\end{code}

%<*TM>
\begin{code}
Tm : Flavour → Style → Ctx → Ty → Set
Tm φ s = Typed.Tm (STLC φ s)

pattern _·_ f e      = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))
pattern lam e        = con (sg `lam (node (_ ∷ []) (e ∷ []) {{refl}}))
pattern lam′ t e     = con (sg `lam (sg t ((node (_ ∷ []) (e ∷ []) {{refl , refl}}))))
pattern letvar e₀ e  = con (sg `let (node (_ ∷ []) (e₀ ∷ e ∷ []) {{refl , refl}}))
\end{code}
%</TM>

%<*DESUGAR>
\begin{code}
desugar : ∀ {s φ Γ} → Tm φ s Γ →̇ Tm desugared s Γ
desugar           (var v)        = var v
desugar           (f · e)        = desugar f · desugar e
desugar {Curry}   (lam e)        = lam (desugar e)
desugar {Church}  (lam′ t e)     = lam′ t (desugar e)
desugar {Curry}   (letvar e₀ e)  = lam (desugar e) · desugar e₀
desugar {Church}  (letvar e₀ e)  = lam′ _ (desugar e) · desugar e₀
\end{code}
%</DESUGAR>
