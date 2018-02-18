\begin{code}[hide]
open import GenericSyntax.Util

module GenericSyntax.Ren.Core (Ty : Set) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import Data.List hiding (drop)
\end{code}

%<*OPE>
\begin{code}
infix 3 _⊇_
data _⊇_ : Ctx → Ctx → Set where
  done : ∅ ⊇ ∅
  drop : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ
  keep : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ , t

ren-var : ∀ {Γ Δ} → Δ ⊇ Γ → Var Γ →̇ Var Δ
\end{code}
%</OPE>

%<*REFL>
\begin{code}
reflᵣ : ∀ {Γ} → Γ ⊇ Γ
reflᵣ {∅}      = done
reflᵣ {Γ , _}  = keep reflᵣ
\end{code}
%</REFL>

\begin{code}
ren-var done       v      = v
ren-var (drop Δ⊇Γ) v      = vs (ren-var Δ⊇Γ v)
ren-var (keep Δ⊇Γ) vz     = vz
ren-var (keep Δ⊇Γ) (vs v) = vs (ren-var Δ⊇Γ v)

wk : ∀ {t Γ} → (Γ , t) ⊇ Γ
wk = drop reflᵣ

_⊇⊇_ : ∀ {Γ Θ Δ} → Γ ⊇ Θ → Θ ⊇ Δ → Γ ⊇ Δ
done       ⊇⊇       Θ⊇Δ  = Θ⊇Δ
(drop Γ⊇Θ) ⊇⊇       Θ⊇Δ  = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (drop Θ⊇Δ) = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (keep Θ⊇Δ) = keep (Γ⊇Θ ⊇⊇ Θ⊇Δ)

drop⋆ : ∀ {Γ Δ} ts → Γ ⊇ Δ → Γ <>< ts ⊇ Δ
drop⋆ []        Γ⊇Δ  = Γ⊇Δ
drop⋆ (_ ∷ ts)  Γ⊇Δ  = drop⋆ ts (drop Γ⊇Δ)

wk⋆ : ∀ {Γ} ts → Γ <>< ts ⊇ Γ
wk⋆ []        = reflᵣ
wk⋆ (x ∷ ts)  = wk⋆ ts ⊇⊇ wk

keep⋆ : ∀ {Γ Δ} ts → Γ ⊇ Δ → Γ <>< ts ⊇ Δ <>< ts
keep⋆ []        Γ⊇Δ = Γ⊇Δ
keep⋆ (_ ∷ ts)  Γ⊇Δ = keep⋆ ts (keep Γ⊇Δ)
\end{code}
