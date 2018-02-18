\begin{code}[hide]
module GenericSyntax.Examples.STLC.Norm where

open import GenericSyntax.Examples.STLC.Core
open import GenericSyntax.Ctx Ty
open import GenericSyntax.Examples.STLC
open import Relation.Binary
open import Data.Star
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function.Equivalence hiding (sym)
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
import GenericSyntax.Repr
open GenericSyntax.Repr.Typed Ty STLC
open import GenericSyntax.Sub.Core Tm
open import GenericSyntax.Sub STLC
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)
open import Level renaming (zero to lzero; suc to lsuc)

\end{code}

%<*Sem>
\begin{code}
data Value : ∀ {Γ t} → Tm Γ t → Set where
  ↓lam : ∀ {Γ t u} → (e : Tm (Γ , u) t) → Value {Γ} {u ▷ t} (lam e)

infix 19 _==>_ _==>⋆_

data _==>_ {Γ} : ∀ {t} → Rel (Tm Γ t) lzero where
  app-lam :  ∀ {t u} {e : Tm _ u} → (f : Tm _ t) → Value e           → lam f · e ==> sub (reflₛ , e) f
  app-fun :  ∀ {t u} {f f′ : Tm _ (u ▷ t)} → f ==> f′ → ∀ e          → f · e ==> f′ · e
  app-arg :  ∀ {t u} {f : Tm _ (u ▷ t)} {e e′} → Value f → e ==> e′  → f · e ==> f · e′

_==>⋆_ : ∀ {Γ t} → Rel (Tm Γ t) _
_==>⋆_ = Star _==>_
\end{code}
%</Sem>

\begin{code}
NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
NF next x = ∄ (next x)

Halts : ∀ {Γ t} → Tm Γ t → Set
Halts e = ∃ λ e′ → e ==>⋆ e′ × Value e′
\end{code}

\begin{code}
module SemProperties where
  value⇒normal : ∀ {Γ t e} → Value {Γ} {t} e → NF _==>_ e
  value⇒normal (↓lam e) (_ , ())

  Deterministic : ∀ {a b} {A : Set a} → Rel A b → Set _
  Deterministic _∼_ = ∀ {x y y′} → x ∼ y → x ∼ y′ → y ≡ y′

  deterministic : ∀ {Γ t} → Deterministic (_==>_ {Γ} {t})
  deterministic (app-lam f _) (app-lam ._ _) = refl
  deterministic (app-lam f v) (app-fun () _)
  deterministic (app-lam f v) (app-arg f′ e) = ⊥-elim (value⇒normal v (, e))
  deterministic (app-fun () e) (app-lam f v)
  deterministic (app-fun f e) (app-fun f′ ._) rewrite deterministic f f′ = refl
  deterministic (app-fun f e) (app-arg f′ _) = ⊥-elim (value⇒normal f′ (, f))
  deterministic (app-arg f e) (app-lam f′ v) = ⊥-elim (value⇒normal v (, e))
  deterministic (app-arg f e) (app-fun f′ _) = ⊥-elim (value⇒normal f (, f′))
  deterministic (app-arg f e) (app-arg f′ e′) rewrite deterministic e e′ = refl

  value⇒halts : ∀ {Γ t e} → Value {Γ} {t} e → Halts e
  value⇒halts {e = e} v = e , ε , v
open SemProperties

module Sat where
  -- -- This would not be strictly positive in the `fun` constructor!
  -- data Saturated : ∀ {Γ t} → Tm Γ t → Set where
  --   fun : ∀ {t u} {f : Tm ∅ (t ▷ u)} → Halts f → (∀ {e} → Saturated e → Saturated (f · e)) → Saturated f
  --   bool : ∀ {b : Tm ∅ Bool} → Halts b → Saturated b

  mutual
    Saturated : ∀ {t} → Tm ∅ t → Set
    Saturated e = Halts e × Saturated′ _ e

    Saturated′ : ∀ t → Tm ∅ t → Set
    Saturated′ ∙ _ = ⊥
    Saturated′ (t ▷ u) f = ∀ {e} → Saturated e → Saturated (f · e)

  saturated⇒halts : ∀ {t e} → Saturated {t} e → Halts e
  saturated⇒halts = proj₁

  step‿preserves‿halting : ∀ {Γ t} {e e′ : Tm Γ t} → e ==> e′ → Halts e ⇔ Halts e′
  step‿preserves‿halting {e = e} {e′ = e′} step = equivalence fwd bwd
    where
      fwd : Halts e → Halts e′
      fwd (e″ , ε , v) = ⊥-elim (value⇒normal v (, step ))
      fwd (e″ , s ◅ steps , v) rewrite deterministic step s = e″ , steps , v

      bwd : Halts e′ → Halts e
      bwd (e″ , steps , v) = e″ , step ◅ steps , v

  step‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e ⇔ Saturated e′
  step‿preserves‿saturated step = equivalence (fwd step) (bwd step)
    where
      fwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e → Saturated e′
      fwd {∙}       step (halts , ())
      fwd {u ▷ t}   step (halts , sat) = Equivalence.to (step‿preserves‿halting step) ⟨$⟩ halts , λ e → fwd (app-fun step _) (sat e)

      bwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e′ → Saturated e
      bwd {∙}       step (halts , ())
      bwd {u ▷ t}   step (halts , sat) = Equivalence.from (step‿preserves‿halting step) ⟨$⟩ halts , λ e → bwd (app-fun step _) (sat e)

  step⋆‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==>⋆ e′ → Saturated e ⇔ Saturated e′
  step⋆‿preserves‿saturated ε = id
  step⋆‿preserves‿saturated (step ◅ steps) = step⋆‿preserves‿saturated steps ∘ step‿preserves‿saturated step
open Sat

open import GenericSyntax.Ren.Core Ty
open import GenericSyntax.Sub.Properties STLC

module Inst where
  data Instantiation : ∀ {Γ} → ∅ ⊢⋆ Γ → Set where
    ∅ : Instantiation ∅
    _,_ : ∀ {Γ t σ} → Instantiation {Γ} σ → ∀ {e} → Value {_} {t} e × Saturated e → Instantiation (σ , e)

  saturate-var : ∀ {Γ σ} → Instantiation σ → ∀ {t} (x : Var Γ t) → Saturated (sub-var σ x)
  saturate-var (_ , (_ , sat)) vz = sat
  saturate-var (env , _) (vs x) = saturate-var env x

  app-lam⋆ : ∀ {Γ t} {e e′ : Tm Γ t} → e ==>⋆ e′ → Value e′ → ∀ {u} (f : Tm _ u) → lam f · e ==>⋆ sub (reflₛ , e′) f
  app-lam⋆ steps v f = gmap _ (app-arg (↓lam _)) steps  ◅◅ app-lam f v ◅ ε

  -- What is a good name for this?
  -- It basically states that you can push in outer arguments before the innermost one.
  -- Should this be called some kind of constant propagation?
  innermost‿last : ∀ {Γ u} (σ : ∅ ⊢⋆ Γ) (e′ : Tm ∅ u) →
    (∅ , e′) ⊢⊢⋆ (wkₛ σ) ≡ σ
  innermost‿last ∅       e′ = refl
  innermost‿last (σ , e) e′ rewrite innermost‿last σ e′ | sym (sub-⊢⋆⊇ (∅ , e′) wk e) | sub-refl e = refl

  saturate : ∀ {Γ σ} → Instantiation σ → ∀ {t} → (e : Tm Γ t) → Saturated (sub σ e)
  saturate         env          (var v)                       = saturate-var env v
  saturate         env          (f · e)                       with saturate env f | saturate env e
  saturate         env          (f · e) | _ , sat-f | sat-e   = sat-f sat-e
  saturate {Γ} {σ} env {u ▷ t}  (lam f)                       = value⇒halts (↓lam (sub (shift σ) f)) , sat-f
    where
      f′ = sub (shift σ) f

      sat-f : ∀ {e : Tm _ u} → Saturated e → Saturated (lam f′ · e)
      sat-f {e} sat-e@((e′ , steps , v) , _) = Equivalence.from (step⋆‿preserves‿saturated f‿e==>f←σe) ⟨$⟩ sat
        where
          f←σe = sub (σ , e′) f
          f′‿e = lam f′ · e

          sat-e′ : Saturated e′
          sat-e′ = Equivalence.to (step⋆‿preserves‿saturated steps) ⟨$⟩ sat-e

          sat : Saturated f←σe
          sat = saturate (env , (v , sat-e′)) f

          f‿e==>f←σe : f′‿e ==>⋆ f←σe
          f‿e==>f←σe = subst (λ f₀ → _ ==>⋆ f₀) lemma (app-lam⋆ steps v (sub (shift σ) f))
            where
              lemma : sub (∅ , e′) (sub (shift σ) f) ≡ sub (σ , e′) f
              lemma rewrite sym ((sub-⊢⊢⋆ (∅ , e′) (shift σ) f)) | innermost‿last σ e′ = refl
open Inst
\end{code}

%<*normalization>
\begin{code}
normalization : ∀ {t} → (e : Tm ∅ t) → Halts e
\end{code}
%</normalization>

\begin{code}
normalization e rewrite sym (sub-refl e) = saturated⇒halts (saturate ∅ e)

\end{code}
