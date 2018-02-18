\begin{code}[hide]
open import GenericSyntax.Util
open import GenericSyntax.Desc

module GenericSyntax.Sub {Ty : Set} (desc : Desc Ty) where

open import GenericSyntax.Ctx Ty
import GenericSyntax.Repr
open GenericSyntax.Repr Ty
open GenericSyntax.Repr.Typed _ desc
open import GenericSyntax.Ren.Core Ty
open import GenericSyntax.Ren desc
open import GenericSyntax.Sub.Core Tm
open import Data.Vec
open import Data.List
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
\end{code}

\begin{code}
infixr 20 _⊇⊢⋆_
_⊇⊢⋆_ : ∀ {Γ Δ Θ} → Θ ⊇ Γ → Γ ⊢⋆ Δ → Θ ⊢⋆ Δ
ρ  ⊇⊢⋆  ∅        = ∅
ρ  ⊇⊢⋆  (σ , e)  = ρ ⊇⊢⋆ σ , ren ρ e

infixl 20 _⊢⋆⊇_
_⊢⋆⊇_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Δ → Δ ⊇ Θ → Γ ⊢⋆ Θ
σ        ⊢⋆⊇  done      = σ
(σ , e)  ⊢⋆⊇  (drop ρ)  = σ ⊢⋆⊇ ρ
(σ , e)  ⊢⋆⊇  (keep ρ)  = σ ⊢⋆⊇ ρ , e

wkₛ : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ
wkₛ σ = wk ⊇⊢⋆ σ

shift : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ , t
shift {t} σ = wk ⊇⊢⋆ σ , var vz

shift⋆ : ∀ {Γ Δ} ts → Γ ⊢⋆ Δ → Γ <>< ts ⊢⋆ Δ <>< ts
shift⋆ [] σ = σ
shift⋆ (t ∷ ts) σ = shift⋆ ts (shift σ)

ren⇒sub : ∀ {Γ Δ} → Γ ⊇ Δ → Γ ⊢⋆ Δ
ren⇒sub done       = ∅
ren⇒sub (drop Γ⊇Δ) = wk ⊇⊢⋆ (ren⇒sub Γ⊇Δ)
ren⇒sub (keep Γ⊇Δ) = shift (ren⇒sub Γ⊇Δ)

reflₛ : ∀ {Γ} → Γ ⊢⋆ Γ
reflₛ {∅}     = ∅
reflₛ {Γ , t} = shift reflₛ
\end{code}

%<*SUB>
\begin{code}
mutual
  sub : ∀ {Γ Δ} → Γ ⊢⋆ Δ → Tm Δ →̇ Tm Γ
  sub σ (var v)  = sub-var σ v
  sub σ (con c)  = con (sub-con σ c)

  sub-con : ∀ {Γ Δ t c} → Γ ⊢⋆ Δ → Con Δ t c → Con Γ t c
  sub-con σ (sg x c)       = sg x (sub-con σ c)
  sub-con σ (node ts₀ es)  = node ts₀ (sub⋆ σ es)

  sub⋆ : ∀ {Γ Δ n k sh ts₀ ts} → Γ ⊢⋆ Δ → Children {n} {k} Δ ts₀ sh ts → Children Γ ts₀ sh ts
  sub⋆                σ  []        = []
  sub⋆ {sh = bs ∷ _}  σ  (e ∷ es)  = sub (shift⋆ (visible bs _) σ) e ∷ sub⋆ σ es
\end{code}
%</SUB>

\begin{code}
_⊢⊢⋆_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Θ → Θ ⊢⋆ Δ → Γ ⊢⋆ Δ
σ ⊢⊢⋆ ∅ = ∅
σ ⊢⊢⋆ (σ′ , e) = (σ ⊢⊢⋆ σ′) , sub σ e
\end{code}
