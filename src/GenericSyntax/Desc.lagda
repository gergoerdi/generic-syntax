\begin{code}[hide]
module GenericSyntax.Desc (Ty : Set) where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Vec
open import Data.Vec.All
open import Function
open import Data.Fin using (Fin)
open import GenericSyntax.Ctx Ty

\end{code}

%<*Desc>
\begin{code}
data Binder : Set where
  bound unbound : Binder

Shape : ℕ → ℕ → Set
Shape n k = Vec (Vec Binder n) k

data Desc : Set₁ where
  sg    : (A : Set) (k : A → Desc) → Desc
  node  : (n : ℕ) {k : ℕ} (shape : Shape n k) (wt : Vec Ty n → Vec Ty k → Ty → Set) → Desc
\end{code}
%</Desc>
