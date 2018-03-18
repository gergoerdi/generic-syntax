\begin{code}[hide]
open import GenericSyntax.Util
import GenericSyntax.Ctx

module GenericSyntax.Sub.Core {Ty : Set} (Tm : GenericSyntax.Ctx.Ctx Ty → Ty → Set) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import GenericSyntax.Env Ty public
open import Data.List hiding (drop)
open import Data.List.All renaming (All to Allₗ) using ([]; _∷_)

infix 3 _⊢⋆_
\end{code}

%<*SSUB>
\begin{code}
_⊢⋆_ : Ctx → Ctx → Set
Γ ⊢⋆ Δ = Env (Tm Γ) Δ

sub-var : ∀ {Γ Δ} → Γ ⊢⋆ Δ → Var Δ →̇ Tm Γ
sub-var = lookup
\end{code}
%</SSUB>
