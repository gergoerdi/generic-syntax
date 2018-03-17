\begin{code}[hide]
open import GenericSyntax.Util

module GenericSyntax.Repr (Ty : Set) where

open import GenericSyntax.Desc Ty
open import Data.Nat
open import Data.List hiding (map; zip)
open import Data.Vec hiding (map; lookup)
open import Data.Vec.All hiding (map; lookup)
open import Data.List.All renaming (All to Allₗ) using (map)
open import Data.Vec.Relation.InductivePointwise
  renaming (Pointwise to All₂)
  hiding (refl; trans; sym; map; lookup)
open import Data.Fin using (Fin)
open import GenericSyntax.Ctx Ty
open import Data.Product hiding (map; zip)
open import Relation.Binary.PropositionalEquality
\end{code}

%<*Unscoped>
\begin{code}
module Unscoped (desc : Desc) (name : Set) where
  mutual
    data Form : Set where
      var  : name      → Form
      con  : Con desc  → Form

    data Con : Desc → Set where
      sg    : ∀ {A k} x → Con (k x) → Con (sg A k)
      node  : ∀ {n k sh wt} (ns : Vec name n) (es : Children k)
        → Con (node n {k} sh wt)

    Children : ℕ → Set
    Children = Vec Form
\end{code}
%</Unscoped>

%<*Untyped>
\begin{code}
countV : ∀ {n} → Vec Binder n → ℕ
countV  []              = 0
countV  (bound ∷ bs)    = suc (countV bs)
countV  (unbound ∷ bs)  = countV bs

module Untyped (desc : Desc) where
  mutual
    data Expr (V : ℕ) : Set where
      var  : Fin V       → Expr V
      con  : Con V desc  → Expr V

    data Con (V : ℕ) : Desc → Set where
      sg    : ∀ {A k} x → Con V (k x) → Con V (sg A k)
      node  : ∀ {n k sh wt} (es : Children V sh)
        → Con V (node n {k} sh wt)

    Children : ∀ {n k} → ℕ → Shape n k → Set
    Children V = All (λ bs → Expr (countV bs + V))
\end{code}
%</Untyped>

%<*Typed>
\begin{code}
visible : ∀ {n} → Vec Binder n → Vec Ty n → List Ty
visible  []              []        = []
visible  (bound ∷ bs)    (t ∷ ts)  = t ∷ visible bs ts
visible  (unbound ∷ bs)  (_ ∷ ts)  = visible bs ts
\end{code}

\begin{code}
module Typed (desc : Desc) where
  mutual
    data Tm (Γ : Ctx) : Ty → Set where
      var  : ∀ {t} → Var Γ t       → Tm Γ t
      con  : ∀ {t} → Con Γ t desc  → Tm Γ t

    data Con (Γ : Ctx) (t : Ty) : Desc → Set where
      sg    : ∀ {A k} x → Con Γ t (k x) → Con Γ t (sg A k)
      node  : ∀ {n k sh wt} (ts₀ : Vec Ty n) {ts : Vec Ty k}
        (es : Children Γ ts₀ sh ts)
        {{_ : wt ts₀ ts t}}
        → Con Γ t (node n sh wt)

    Children : ∀ {n k} → Ctx → Vec Ty n → Shape n k → Vec Ty k → Set
    Children Γ ts₀ = All₂ (λ bs → Tm (Γ <>< visible bs ts₀))
\end{code}
%</Typed>

%<*untype>
\begin{code}[hide]
size : Ctx → ℕ
size ∅       = 0
size (Γ , _) = suc (size Γ)

x+sy≡sx+y : ∀ x y → x + suc y ≡ suc x + y
x+sy≡sx+y zero     y  = refl
x+sy≡sx+y (suc x)  y  rewrite x+sy≡sx+y x y = refl

size-<>< : ∀ {n} (Γ : Ctx) (bs : Vec Binder n) (ts : Vec Ty n) → size (Γ <>< visible bs ts) ≡ countV bs + size Γ
size-<><          Γ  []              []        = refl
size-<>< {suc n}  Γ  (unbound ∷ bs)  (t ∷ ts)  rewrite size-<>< Γ bs ts = refl
size-<>< {suc n}  Γ  (bound ∷ bs)    (t ∷ ts)  rewrite size-<>< (Γ , t) bs ts = x+sy≡sx+y (countV bs) (size Γ)

module Untype (desc : Desc) where

  module T = Typed desc
  module U = Untyped desc
  open T
  open U
  open import Data.Fin using (zero; suc)
\end{code}

\begin{code}
  untype-var : ∀ {Γ t} → Var Γ t → Fin (size Γ)
  untype-var vz     = zero
  untype-var (vs v) = suc (untype-var v)

  untype : ∀ {Γ t} → Tm Γ t → Expr (size Γ)
  untype (var v) = var (untype-var v)
  untype (con e) = con (untype-con e)
    where
      untype⋆ : ∀ {Γ n k sh ts₀ ts} → T.Children {n} {k} Γ ts₀ sh ts → U.Children (size Γ) sh
      untype⋆                []        = []
      untype⋆ {sh = bs ∷ _}  (e ∷ es)  = subst Expr (size-<>< _ bs _) (untype e) ∷ untype⋆ es

      untype-con : ∀ {Γ t c} → T.Con Γ t c → U.Con (size Γ) c
      untype-con (sg x e)       = sg x (untype-con e)
      untype-con (node ts₀ es)  = node (untype⋆ es)
\end{code}
%</untype>

%<*phoas>
\begin{code}
module PHOAS (desc : Desc) where
  mutual
    data Tm (V : Ty → Set) : Ty → Set where
      var : ∀ {t}  → V t           → Tm V t
      con : ∀ {t}  → Con V t desc  → Tm V t

    data Con (V : Ty → Set) (t : Ty) : Desc → Set where
      sg : ∀ {A k} x → Con V t (k x) → Con V t (sg A k)
      node : ∀ {n k sh wt} (ts₀ : Vec Ty n) {ts : Vec Ty k}
        (es : Children V ts₀ sh ts)
        {{_ : wt ts₀ ts t}}
        → Con V t (node n sh wt)

    Children : ∀ {n k} → (Ty → Set) → Vec Ty n → Shape n k → Vec Ty k → Set
    Children V ts₀ = All₂ (λ bs t → (Allₗ V (visible bs ts₀) → Tm V t))
\end{code}
%</phoas>

\begin{code}
    sub : ∀ {V} → Tm (Tm V) →̇ Tm V
    sub (var v)  = v
    sub (con c)  = con (sub-con c)
      where
        sub⋆ : ∀ {V n k sh ts₀ ts} → Children {n} {k} (Tm V) ts₀ sh ts → Children V ts₀ sh ts
        sub⋆ []        = []
        sub⋆ (e ∷ es)  = (λ xs → sub (e (map var xs))) ∷ sub⋆ es

        sub-con : ∀ {V t c} → Con (Tm V) t c → Con V t c
        sub-con (sg x c)       = sg x (sub-con c)
        sub-con (node ts₀ es)  = node ts₀ (sub⋆ es)
\end{code}
