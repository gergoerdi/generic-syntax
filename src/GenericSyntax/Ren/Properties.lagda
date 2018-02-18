\begin{code}[hide]
import GenericSyntax.Desc

module GenericSyntax.Ren.Properties {Ty : Set} (desc : GenericSyntax.Desc.Desc Ty) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import GenericSyntax.Ren.Core Ty
open import GenericSyntax.Ren.Core.Properties Ty
open import GenericSyntax.Ren desc
open import GenericSyntax.Repr Ty
open Typed desc
open import Data.Vec.All
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Function
\end{code}

%<*REN-REFL>
\begin{code}
mutual
  ren-refl : ∀ {Γ t} → (e : Tm Γ t) → ren reflᵣ e ≡ e
  ren-refl (var v)  rewrite ren-var-refl v = refl
  ren-refl (con e)  rewrite ren-con-refl e = refl

  ren-con-refl : ∀ {c Γ t} (e : Con Γ t c) → ren-con reflᵣ e ≡ e
  ren-con-refl (sg x e)      rewrite ren-con-refl e  = refl
  ren-con-refl (node ts es)  rewrite ren⋆-refl es = refl

  ren⋆-refl : ∀ {Γ n k sh ts₀ ts} (es : Children {n} {k} Γ ts₀ sh ts) → ren⋆ reflᵣ es ≡ es
  ren⋆-refl                          []        = refl
  ren⋆-refl {Γ} {sh = bs ∷ _} {ts₀}  (e ∷ es)  rewrite keep⋆-refl {Γ} (visible bs ts₀) =
    cong₂ _∷_ (ren-refl e) (ren⋆-refl es)
\end{code}
%</REN-REFL>

\begin{code}
mutual
  ren-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Tm Δ t) →
    ren Γ⊇Θ (ren Θ⊇Δ e) ≡ ren (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (var v) rewrite ren-var-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (con e) rewrite ren-con-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl

  ren-con-⊇⊇ : ∀ {Γ Θ Δ t c} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Con Δ t c) →
    ren-con Γ⊇Θ (ren-con Θ⊇Δ e) ≡ ren-con (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  ren-con-⊇⊇ Γ⊇Θ Θ⊇Δ (sg x e)     rewrite ren-con-⊇⊇ Γ⊇Θ Θ⊇Δ e  = refl
  ren-con-⊇⊇ Γ⊇Θ Θ⊇Δ (node ts es) rewrite ren⋆-⊇⊇ Γ⊇Θ Θ⊇Δ es = refl

  ren⋆-⊇⊇ : ∀ {Γ Θ Δ n k sh ts₀ ts} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (es : Children {n} {k} Δ ts₀ sh ts) →
    ren⋆ Γ⊇Θ (ren⋆ Θ⊇Δ es) ≡ ren⋆ (Γ⊇Θ ⊇⊇ Θ⊇Δ) es
  ren⋆-⊇⊇ Γ⊇Θ Θ⊇Δ [] = refl
  ren⋆-⊇⊇ {sh = bs ∷ _} {ts₀} Γ⊇Θ Θ⊇Δ (e ∷ es) rewrite
    ren-⊇⊇ (keep⋆ (visible bs ts₀) Γ⊇Θ) (keep⋆ (visible bs ts₀) Θ⊇Δ) e |
    keep⋆-⊇⊇ (visible bs ts₀) Γ⊇Θ Θ⊇Δ |
    ren⋆-⊇⊇ Γ⊇Θ Θ⊇Δ es
    = refl
\end{code}
