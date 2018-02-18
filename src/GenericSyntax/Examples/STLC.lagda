\begin{code}[hide]
open import GenericSyntax.Util

module GenericSyntax.Examples.STLC where

open import GenericSyntax.Examples.STLC.Core
open import GenericSyntax.Desc Ty
open import GenericSyntax.Repr Ty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
open import Data.Vec using ([]; _∷_)
\end{code}

%<*Typed>
\begin{code}
open Typed STLC

-- _·_ : ∀ {Γ t u} → Tm Γ (t ▷ u) → Tm Γ t → Tm Γ u
pattern _·_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))

-- lam : ∀ {Γ t u} → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern lam e = con (sg `lam (node (_ ∷ []) (e ∷ []) {{refl}}))
\end{code}
%</Typed>
