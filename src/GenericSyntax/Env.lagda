\begin{code}[hide]
open import GenericSyntax.Util

import GenericSyntax.Ctx

module GenericSyntax.Env (Ty : Set) where

open import GenericSyntax.Ctx Ty
open import Data.List.All renaming (All to Allₗ) using ([]; _∷_)

infixr 4 _,_
\end{code}

%<*ENV>
\begin{code}
data Env (A : Ty → Set) : Ctx → Set where
  ∅ : Env A ∅
  _,_ : ∀ {t Δ} → (σ : Env A Δ) → (e : A t) → Env A (Δ , t)

lookup : ∀ {A Δ} → Env A Δ → Var Δ →̇ A
\end{code}
%</ENV>

\begin{code}
lookup (σ , e)  vz      = e
lookup (σ , e)  (vs v)  = lookup σ v

extend : ∀ {A Δ ts} → Env A Δ → Allₗ A ts → Env A (Δ <>< ts)
extend σ  []        = σ
extend σ  (x ∷ xs)  = extend (σ , x) xs
\end{code}
