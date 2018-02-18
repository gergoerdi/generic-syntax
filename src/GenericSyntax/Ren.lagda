\begin{code}[hide]
open import GenericSyntax.Util
import GenericSyntax.Desc

module GenericSyntax.Ren {Ty : Set} (desc : GenericSyntax.Desc.Desc Ty) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
import GenericSyntax.Repr
open GenericSyntax.Repr Ty
open GenericSyntax.Repr.Typed _ desc
open import GenericSyntax.Ren.Core Ty
open import Data.Vec.All
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
\end{code}

%<*REN>
\begin{code}
mutual
  ren : ∀ {Γ Δ} → Γ ⊇ Δ → Tm Δ →̇ Tm Γ
  ren ρ (var v)  = var (ren-var ρ v)
  ren ρ (con c)  = con (ren-con ρ c)

  ren-con : ∀ {d Γ Δ t} → Γ ⊇ Δ → Con Δ t d → Con Γ t d
  ren-con ρ (sg x k)       = sg x (ren-con ρ k)
  ren-con ρ (node ts₀ es)  = node ts₀ (ren⋆ ρ es)

  ren⋆ : ∀ {Γ Δ} {n k ts₀ sh ts} → Γ ⊇ Δ → Children {n} {k} Δ ts₀ sh ts → Children Γ ts₀ sh ts
  ren⋆                ρ  []        = []
  ren⋆ {sh = bs ∷ _}  ρ  (e ∷ es)  = ren (keep⋆ (visible bs _) ρ) e ∷ ren⋆ ρ es
\end{code}
%</REN>
