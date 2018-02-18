\begin{code}[hide]
open import GenericSyntax.Util
import GenericSyntax.Ctx

module GenericSyntax.Sub.Core {Ty : Set} (Tm : GenericSyntax.Ctx.Ctx Ty → Ty → Set) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import Data.List hiding (drop)

infixr 4 _,_
infix 3 _⊢⋆_
\end{code}

%<*SSUB>
\begin{code}
data _⊢⋆_ (Γ : Ctx) : Ctx → Set where
  ∅ : Γ ⊢⋆ ∅
  _,_ : ∀ {t Δ} → (σ : Γ ⊢⋆ Δ) → (e : Tm Γ t) → Γ ⊢⋆ Δ , t

sub-var : ∀ {Γ Δ} → Γ ⊢⋆ Δ → Var Δ →̇ Tm Γ
\end{code}
%</SSUB>

\begin{code}
sub-var (σ , e) vz     = e
sub-var (σ , e) (vs v) = sub-var σ v
\end{code}
