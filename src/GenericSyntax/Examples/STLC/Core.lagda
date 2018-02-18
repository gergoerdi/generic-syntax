\begin{code}
module GenericSyntax.Examples.STLC.Core where

open import Data.Nat
open import Data.Fin using (Fin)
open import Relation.Nullary
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
open import Data.Vec

\end{code}

infixr 20 _▷_
%<*Ty>
\begin{code}
data Ty : Set where
  ∙    :  Ty
  _▷_  :  Ty → Ty → Ty
\end{code}
%</Ty>

\begin{code}
open import GenericSyntax.Desc Ty
\end{code}

%<*APP>
\begin{code}
APP : Desc
APP = node 0 ([] ∷ [] ∷ [])
  λ { [] (t₁ ∷ t₂ ∷ []) t₀ → t₁ ≡ t₂ ▷ t₀ }
\end{code}
%</APP>

%<*LAM>
\begin{code}
data Style : Set where
  Curry Church : Style

LAM_style : Style → Desc
LAM Curry style = node 1 ((bound ∷ []) ∷ [])
  λ { (t′ ∷ []) (u ∷ []) t₀ → t₀ ≡ t′ ▷ u }
LAM Church style = sg Ty λ t → node 1 ((bound ∷ []) ∷ [])
  λ { (t′ ∷ []) (u ∷ []) t₀ → t ≡ t′ × t₀ ≡ t ▷ u }
\end{code}
%</LAM>

%<*LET>
\begin{code}
LET : Desc
LET = node 1 ((unbound ∷ []) ∷ (bound ∷ []) ∷ [])
  λ { (u ∷ []) (u′ ∷ t′ ∷ []) t₀ → u ≡ u′ × t₀ ≡ t′ }
\end{code}
%</LET>

%<*LETREC>
\begin{code}
LETREC : Desc
LETREC = node 1 ((bound ∷ []) ∷ (bound ∷ []) ∷ [])
  λ { (u ∷ []) (u′ ∷ t′ ∷ []) t₀ → u ≡ u′ × t₀ ≡ t′ }
\end{code}
%</LETREC>

%<*Desc>
\begin{code}
data `STLC : Set where
  `app `lam : `STLC

STLC : Desc
STLC = sg `STLC λ
  {  `app  →  APP
  ;  `lam  →  LAM Curry style
  }
\end{code}
%</Desc>
