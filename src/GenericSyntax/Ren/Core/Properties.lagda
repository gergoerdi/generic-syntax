\begin{code}[hide]
module GenericSyntax.Ren.Core.Properties (Ty : Set) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import GenericSyntax.Ren.Core Ty
open import Data.List hiding (drop)
open import Relation.Binary.PropositionalEquality

keep⋆-refl : ∀ {Γ} ts → keep⋆ ts (reflᵣ {Γ}) ≡ reflᵣ
keep⋆-refl {Γ} []        = refl
keep⋆-refl {Γ} (t ∷ ts) = keep⋆-refl {Γ , t} ts

keep⋆-⊇⊇ : ∀ {Γ Δ Θ} ts (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) →
           keep⋆ ts (Γ⊇Θ ⊇⊇ Θ⊇Δ) ≡ (keep⋆ ts Γ⊇Θ) ⊇⊇ (keep⋆ ts Θ⊇Δ)
keep⋆-⊇⊇ []       Γ⊇Θ Θ⊇Δ = refl
keep⋆-⊇⊇ (t ∷ ts) Γ⊇Θ Θ⊇Δ = keep⋆-⊇⊇ ts (keep {t} Γ⊇Θ) (keep {t} Θ⊇Δ)

refl-⊇⊇_ : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  reflᵣ ⊇⊇ Γ⊇Δ ≡ Γ⊇Δ
refl-⊇⊇ done     = refl
refl-⊇⊇ drop Γ⊇Δ rewrite refl-⊇⊇ Γ⊇Δ = refl
refl-⊇⊇ keep Γ⊇Δ rewrite refl-⊇⊇ Γ⊇Δ = refl

_⊇⊇-refl : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  Γ⊇Δ ⊇⊇ reflᵣ ≡ Γ⊇Δ
done     ⊇⊇-refl = refl
drop Γ⊇Δ ⊇⊇-refl rewrite Γ⊇Δ ⊇⊇-refl = refl
keep Γ⊇Δ ⊇⊇-refl rewrite Γ⊇Δ ⊇⊇-refl = refl

⊇-assoc : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (Δ⊇Θ : Δ ⊇ Θ) (Θ⊇Ξ : Θ ⊇ Ξ) →
  (Γ⊇Δ ⊇⊇ Δ⊇Θ) ⊇⊇ Θ⊇Ξ ≡ Γ⊇Δ ⊇⊇ (Δ⊇Θ ⊇⊇ Θ⊇Ξ)
⊇-assoc done             Δ⊇Θ        Θ⊇Ξ  = refl
⊇-assoc (drop Γ⊇Δ)       Δ⊇Θ        Θ⊇Ξ  rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (drop Δ⊇Θ)       Θ⊇Ξ  rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (keep Δ⊇Θ) (drop Θ⊇Ξ) rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (keep Δ⊇Θ) (keep Θ⊇Ξ) rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl

ren-var-refl : ∀ {Γ t} (v : Var t Γ) → ren-var reflᵣ v ≡ v
ren-var-refl vz     = refl
ren-var-refl (vs v) rewrite ren-var-refl v = refl

ren-var-⊇⊇ : ∀ {Γ Θ Δ} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) {t} (v : Var Δ t) →
  ren-var Γ⊇Θ (ren-var Θ⊇Δ v) ≡ ren-var (Γ⊇Θ ⊇⊇ Θ⊇Δ) v
ren-var-⊇⊇ done             Θ⊇Δ  v      = refl
ren-var-⊇⊇ (drop Γ⊇Θ)       Θ⊇Δ  v      rewrite ren-var-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
ren-var-⊇⊇ (keep Γ⊇Θ) (drop Θ⊇Δ) v      rewrite ren-var-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
ren-var-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) vz     = refl
ren-var-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) (vs v) rewrite ren-var-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
\end{code}
