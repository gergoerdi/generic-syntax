\begin{code}[hide]
module GenericSyntax.Examples.STLC.Bool where

open import Data.Nat
open import Data.Fin using (Fin)
open import Relation.Nullary
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)

\end{code}

infixr 20 _▷_
%<*Ty>
\begin{code}
data Ty : Set where
  ∙    :  Ty
  _▷_  :  Ty → Ty → Ty
  bool :  Ty
\end{code}
%</Ty>

\begin{code}
open import GenericSyntax.Desc Ty
open import GenericSyntax.Repr Ty
\end{code}

%<*desc>
\begin{code}
data `STLC : Set where
  `app `lam `true `false `if : `STLC

STLC : Desc
STLC = sg `STLC λ
  { `app    →  node 0 ([] ∷ [] ∷ [])       λ { []        (t₁ ∷ t₂ ∷ [])      t₀  → t₁  ≡ t₂ ▷ t₀ }
  ; `lam    →  node 1 ((bound ∷ []) ∷ [])  λ { (t ∷ [])  (u ∷ [])            t₀  → t₀  ≡ t ▷ u }
  ; `true   →  node 0 []                   λ { []        []                  t₀  → t₀  ≡ bool }
  ; `false  →  node 0 []                   λ { []        []                  t₀  → t₀  ≡ bool }
  ; `if     →  node 0 ([] ∷ [] ∷ [] ∷ [])  λ { []        (b ∷ t₁ ∷ t₂ ∷ [])  t₀  → b   ≡ bool × t₁ ≡ t₀ × t₂ ≡ t₀ }
  }
\end{code}
%</desc>

\begin{code}
open Typed STLC public

-- _·_ : ∀ {Γ t u} → Tm Γ (t ▷ u) → Tm Γ t → Tm Γ u
pattern _·_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))

-- lam : ∀ {Γ t u} → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern lam e = con (sg `lam (node (_ ∷ []) (e ∷ []) {{refl}}))

pattern true = con (sg `true (node [] [] {{refl}}))
pattern false = con (sg `false (node [] [] {{refl}}))
pattern if b thn els = con (sg `if (node [] (b ∷ thn ∷ els ∷ []) {{refl , refl , refl}}))
\end{code}
