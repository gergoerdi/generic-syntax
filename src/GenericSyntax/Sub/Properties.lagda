\begin{code}[hide]
import GenericSyntax.Desc

module GenericSyntax.Sub.Properties {Ty : Set} (desc : GenericSyntax.Desc.Desc Ty) where

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty
open import GenericSyntax.Ren.Core Ty
open import GenericSyntax.Ren.Core.Properties Ty
open import GenericSyntax.Ren desc
open import GenericSyntax.Ren.Properties desc
open import GenericSyntax.Repr Ty
open Typed desc
open import GenericSyntax.Sub.Core Tm
open import GenericSyntax.Sub desc
open import Data.Vec.All using ([]; _∷_)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.List using ([]; _∷_)
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
\end{code}

\begin{code}
assocᵣᵣₛ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (Δ⊇Θ ⊇⊢⋆ σ) ≡ (Γ⊇Δ ⊇⊇ Δ⊇Θ) ⊇⊢⋆ σ
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ ∅ = refl
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ (σ , e) rewrite assocᵣᵣₛ Γ⊇Δ Δ⊇Θ σ | ren-⊇⊇ Γ⊇Δ Δ⊇Θ e = refl

assocᵣₛᵣ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (Θ⊇Ξ : Θ ⊇ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⋆⊇ Θ⊇Ξ) ≡  (Γ⊇Δ ⊇⊢⋆ σ) ⊢⋆⊇ Θ⊇Ξ
assocᵣₛᵣ Γ⊇Δ σ       done       = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (drop Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (keep Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl

shift⋆-keep⋆ : ∀ {Γ Δ Θ} ts (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) →
  shift⋆ ts (σ ⊢⋆⊇ Δ⊇Θ) ≡ shift⋆ ts σ ⊢⋆⊇ keep⋆ ts Δ⊇Θ
shift⋆-keep⋆ [] σ Δ⊇Θ = refl
shift⋆-keep⋆ (t ∷ ts) σ Δ⊇Θ rewrite assocᵣₛᵣ (drop {t} reflᵣ) σ Δ⊇Θ = shift⋆-keep⋆ ts (shift σ) (keep Δ⊇Θ)

keep⋆-shift⋆ : ∀ {Γ Δ Θ} ts (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) →
  shift⋆ ts (Γ⊇Δ ⊇⊢⋆ σ) ≡ keep⋆ ts Γ⊇Δ ⊇⊢⋆ shift⋆ ts σ
keep⋆-shift⋆ []       Γ⊇Δ σ = refl
keep⋆-shift⋆ (t ∷ ts) Γ⊇Δ σ rewrite
  assocᵣᵣₛ (wk {t}) Γ⊇Δ σ |
  refl-⊇⊇ Γ⊇Δ | sym (Γ⊇Δ ⊇⊇-refl) |
  sym (assocᵣᵣₛ (keep {t} Γ⊇Δ) wk σ) | Γ⊇Δ ⊇⊇-refl
  = keep⋆-shift⋆ ts (keep Γ⊇Δ) (shift σ)

refl-⊇⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) →
  reflᵣ ⊇⊢⋆ σ ≡ σ
refl-⊇⊢⋆  ∅        = refl
refl-⊇⊢⋆  (σ , e)  rewrite refl-⊇⊢⋆ σ | ren-refl e = refl

_⊇⊢⋆-refl : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) → Γ⊇Δ ⊇⊢⋆ reflₛ ≡ ren⇒sub Γ⊇Δ
done          ⊇⊢⋆-refl  = refl
drop {t} Γ⊇Δ  ⊇⊢⋆-refl  rewrite
  sym (refl-⊇⊇ Γ⊇Δ) |
  sym (assocᵣᵣₛ (wk {t}) Γ⊇Δ reflₛ) | Γ⊇Δ ⊇⊢⋆-refl |
  refl-⊇⊇ Γ⊇Δ
  = refl
keep {t} Γ⊇Δ  ⊇⊢⋆-refl  rewrite
  assocᵣᵣₛ (keep {t} Γ⊇Δ) (drop reflᵣ) reflₛ |
  Γ⊇Δ ⊇⊇-refl | (drop {t} Γ⊇Δ) ⊇⊢⋆-refl
  = refl

_⊢⋆⊇-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⋆⊇ reflᵣ ≡ σ
∅        ⊢⋆⊇-refl  = refl
(σ , e)  ⊢⋆⊇-refl  rewrite σ ⊢⋆⊇-refl = refl

refl-⊢⋆⊇_ : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  reflₛ ⊢⋆⊇ Γ⊇Δ ≡ ren⇒sub Γ⊇Δ
refl-⊢⋆⊇  done            = refl
refl-⊢⋆⊇  (drop {t} Γ⊇Δ)  rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl
refl-⊢⋆⊇  (keep {t} Γ⊇Δ)  rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl

sub-var-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (v : Var Θ t) →
  sub-var (σ ⊢⋆⊇ Δ⊇Θ) v ≡ sub-var σ (ren-var Δ⊇Θ v)
sub-var-⊢⋆⊇  σ        done        v       = refl
sub-var-⊢⋆⊇  (σ , e)  (drop Δ⊇Θ)  v       rewrite sub-var-⊢⋆⊇ σ Δ⊇Θ v = refl
sub-var-⊢⋆⊇  (σ , e)  (keep Δ⊇Θ)  vz      = refl
sub-var-⊢⋆⊇  (σ , e)  (keep Δ⊇Θ)  (vs v)  rewrite sub-var-⊢⋆⊇ σ Δ⊇Θ v = refl

mutual
  sub-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Tm Θ t) →
    sub (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub σ (ren Δ⊇Θ e)
  sub-⊢⋆⊇ σ Δ⊇Θ (var v)  rewrite sub-var-⊢⋆⊇ σ Δ⊇Θ v = refl
  sub-⊢⋆⊇ σ Δ⊇Θ (con e)  rewrite sub-con-⊢⋆⊇ σ Δ⊇Θ e = refl

  sub-con-⊢⋆⊇ : ∀ {Γ Δ Θ t c} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Con Θ t c) →
    sub-con (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub-con σ (ren-con Δ⊇Θ e)
  sub-con-⊢⋆⊇ σ Δ⊇Θ  (sg x e)      rewrite sub-con-⊢⋆⊇ σ Δ⊇Θ e = refl
  sub-con-⊢⋆⊇ σ Δ⊇Θ  (node ts es)  rewrite sub⋆-⊢⋆⊇ σ Δ⊇Θ es = refl

  sub⋆-⊢⋆⊇ : ∀ {Γ Δ Θ n k sh ts₀ ts} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (es : Children {n} {k} Θ ts₀ sh ts) →
    sub⋆ (σ ⊢⋆⊇ Δ⊇Θ) es ≡ sub⋆ σ (ren⋆ Δ⊇Θ es)
  sub⋆-⊢⋆⊇                      σ  Δ⊇Θ  []        = refl
  sub⋆-⊢⋆⊇ {sh = bs ∷ _} {ts₀}  σ  Δ⊇Θ  (e ∷ es)  rewrite
    shift⋆-keep⋆ (visible bs ts₀) σ Δ⊇Θ |
    sub-⊢⋆⊇ (shift⋆ (visible bs ts₀) σ) (keep⋆ (visible bs ts₀) Δ⊇Θ) e |
    sub⋆-⊢⋆⊇ σ Δ⊇Θ es
    = refl

sub-var-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (v : Var Θ t) →
  sub-var (Γ⊇Δ ⊇⊢⋆ σ) v ≡ ren Γ⊇Δ (sub-var σ v)
sub-var-⊇⊢⋆ Γ⊇Δ (σ , _) vz      = refl
sub-var-⊇⊢⋆ Γ⊇Δ (σ , _) (vs v)  = sub-var-⊇⊢⋆ Γ⊇Δ σ v

mutual
  sub-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Tm Θ t) →
    sub (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren Γ⊇Δ (sub σ e)
  sub-⊇⊢⋆ σ Δ⊇Θ (var v)  rewrite sub-var-⊇⊢⋆ σ Δ⊇Θ v = refl
  sub-⊇⊢⋆ σ Δ⊇Θ (con e)  rewrite sub-con-⊇⊢⋆ σ Δ⊇Θ e = refl

  sub-con-⊇⊢⋆ : ∀ {Γ Δ Θ t c} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Con Θ t c) →
    sub-con (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren-con Γ⊇Δ (sub-con σ e)
  sub-con-⊇⊢⋆ Γ⊇Δ σ (sg x e)      rewrite sub-con-⊇⊢⋆ Γ⊇Δ σ e = refl
  sub-con-⊇⊢⋆ Γ⊇Δ σ (node ts es)  rewrite sub⋆-⊇⊢⋆ Γ⊇Δ σ es = refl

  sub⋆-⊇⊢⋆ : ∀ {Γ Δ Θ n k sh ts₀ ts} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (es : Children {n} {k} Θ ts₀ sh ts) →
    sub⋆ (Γ⊇Δ ⊇⊢⋆ σ) es ≡ ren⋆ Γ⊇Δ (sub⋆ σ es)
  sub⋆-⊇⊢⋆                      Γ⊇Δ  σ  []        = refl
  sub⋆-⊇⊢⋆ {sh = bs ∷ _} {ts₀}  Γ⊇Δ  σ  (e ∷ es)  rewrite
    keep⋆-shift⋆ (visible bs ts₀) Γ⊇Δ σ |
    sub-⊇⊢⋆ (keep⋆ (visible bs ts₀) Γ⊇Δ) (shift⋆ (visible bs ts₀) σ) e |
    sub⋆-⊇⊢⋆ Γ⊇Δ σ es
    = refl

assocₛᵣₛ : ∀ {Γ Δ Θ Ξ} (ρ : Θ ⊢⋆ Ξ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Γ ⊢⋆ Δ) →
  σ ⊢⊢⋆ (Δ⊇Θ ⊇⊢⋆ ρ) ≡ (σ ⊢⋆⊇ Δ⊇Θ) ⊢⊢⋆ ρ
assocₛᵣₛ ∅        Δ⊇Θ  σ  = refl
assocₛᵣₛ (ρ , e)  Δ⊇Θ  σ  rewrite assocₛᵣₛ ρ Δ⊇Θ σ | sym (sub-⊢⋆⊇ σ Δ⊇Θ e) = refl

assocᵣₛₛ :  ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⊢⋆ ρ) ≡ (Γ⊇Δ ⊇⊢⋆ σ) ⊢⊢⋆ ρ
assocᵣₛₛ Γ⊇Δ σ  ∅        = refl
assocᵣₛₛ Γ⊇Δ σ  (ρ , e)  rewrite assocᵣₛₛ Γ⊇Δ σ ρ | sym (sub-⊇⊢⋆ Γ⊇Δ σ e) = refl

sub-var-refl : ∀ {Γ t} (v : Var t Γ) → sub-var reflₛ v ≡ var v
sub-var-refl vz           = refl
sub-var-refl (vs {u} v)   rewrite sub-var-⊇⊢⋆ (wk {u}) reflₛ v | sub-var-refl v | ren-var-refl v = refl

shift⋆-refl : ∀ {Γ} ts → shift⋆ ts (reflₛ {Γ}) ≡ reflₛ
shift⋆-refl {Γ}  []        = refl
shift⋆-refl {Γ}  (t ∷ ts)  = shift⋆-refl {Γ , t} ts

mutual
  sub-refl : ∀ {Γ t} (e : Tm Γ t) → sub reflₛ e ≡ e
  sub-refl (var v)  rewrite sub-var-refl v = refl
  sub-refl (con e)  rewrite sub-con-refl e = refl

  sub-con-refl : ∀ {Γ t c} (e : Con Γ t c) → sub-con reflₛ e ≡ e
  sub-con-refl (sg x e)     rewrite sub-con-refl e = refl
  sub-con-refl (node s es)  rewrite sub⋆-refl es = refl

  sub⋆-refl : ∀ {Γ n k sh ts₀ ts} (es : Children {n} {k} Γ ts₀ sh ts) → sub⋆ reflₛ es ≡ es
  sub⋆-refl                          []        = refl
  sub⋆-refl {Γ} {sh = bs ∷ _} {ts₀}  (e ∷ es)  rewrite shift⋆-refl {Γ} (visible bs ts₀) = cong₂ _∷_ (sub-refl _) (sub⋆-refl _)

sub-var-⊢⊢⋆  : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (v : Var Δ t) →
  sub-var (σ ⊢⊢⋆ ρ) v ≡ sub σ (sub-var ρ v)
sub-var-⊢⊢⋆ σ (ρ , _)  vz      = refl
sub-var-⊢⊢⋆ σ (ρ , _)  (vs v)  = sub-var-⊢⊢⋆ σ ρ v

shift⋆-⊢⊢⋆ : ∀ {Γ Δ Θ} ts (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) → shift⋆ ts (σ ⊢⊢⋆ ρ) ≡ shift⋆ ts σ ⊢⊢⋆ shift⋆ ts ρ
shift⋆-⊢⊢⋆  []        σ ρ  = refl
shift⋆-⊢⊢⋆  (t ∷ ts)  σ ρ  rewrite
  assocᵣₛₛ (wk {t}) σ ρ |
  cong (_⊢⊢⋆ ρ) (sym ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl)) |
  sym (assocₛᵣₛ ρ (wk {t}) (shift σ))
  = shift⋆-⊢⊢⋆ ts (wk ⊇⊢⋆ σ , var vz) (wk ⊇⊢⋆ ρ , var vz)

mutual
  sub-⊢⊢⋆ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Tm Δ t) →
    sub (σ ⊢⊢⋆ ρ) e ≡ sub σ (sub ρ e)
  sub-⊢⊢⋆ σ ρ  (var v)  rewrite sub-var-⊢⊢⋆ σ ρ v = refl
  sub-⊢⊢⋆ σ ρ  (con e)  rewrite sub-con-⊢⊢⋆ σ ρ e = refl

  sub-con-⊢⊢⋆ : ∀ {Γ Δ Θ t c} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Con Δ t c) →
    sub-con (σ ⊢⊢⋆ ρ) e ≡ sub-con σ (sub-con ρ e)
  sub-con-⊢⊢⋆ σ ρ  (sg x e)     rewrite sub-con-⊢⊢⋆ σ ρ e = refl
  sub-con-⊢⊢⋆ σ ρ  (node s es)  rewrite sub⋆-⊢⊢⋆ σ ρ es = refl

  sub⋆-⊢⊢⋆ : ∀ {Γ Δ Θ n k sh ts₀ ts} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (es : Children {n} {k} Δ ts₀ sh ts) →
    sub⋆ (σ ⊢⊢⋆ ρ) es ≡ sub⋆ σ (sub⋆ ρ es)
  sub⋆-⊢⊢⋆                      σ  ρ  []        = refl
  sub⋆-⊢⊢⋆ {sh = bs ∷ _} {ts₀}  σ  ρ  (e ∷ es)  rewrite
    shift⋆-⊢⊢⋆ (visible bs ts₀) σ ρ
    = cong₂ _∷_ (sub-⊢⊢⋆ _ _ e) (sub⋆-⊢⊢⋆ _ _ es)

refl-⊢⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → reflₛ ⊢⊢⋆ σ ≡ σ
refl-⊢⊢⋆  ∅        = refl
refl-⊢⊢⋆  (σ , e)  rewrite refl-⊢⊢⋆ σ | sub-refl e = refl

_⊢⊢⋆-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⊢⋆ reflₛ ≡ σ
∅        ⊢⊢⋆-refl  = refl
(σ , e)  ⊢⊢⋆-refl  rewrite assocₛᵣₛ reflₛ wk (σ , e) | σ ⊢⋆⊇-refl | σ ⊢⊢⋆-refl = refl

\end{code}
