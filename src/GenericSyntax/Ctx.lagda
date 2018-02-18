\begin{code}[hide]
module GenericSyntax.Ctx (Ty : Set) where

open import Data.List
\end{code}

%<*CTX>
\begin{code}
data Ctx : Set where
  ∅    :  Ctx
  _,_  :  Ctx → Ty → Ctx

data Var : Ctx → Ty → Set where
  vz  :  ∀  {t}    {Γ}                → Var (Γ , t) t
  vs  :  ∀  {u t}  {Γ} (v : Var Γ t)  → Var (Γ , u) t
\end{code}
%</CTX>

%<*fish>
\begin{code}
_<><_ : Ctx → List Ty → Ctx
Γ <>< [] = Γ
Γ <>< (t ∷ ts) = (Γ , t) <>< ts
\end{code}
%</fish>
