open import GenericSyntax.Util

module GenericSyntax.Examples.Hutton  where

open import Data.Integer
open import Data.Bool
open import Data.Vec
open import Data.Vec.All
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _∷_; [])
open import Data.Vec.Relation.InductivePointwise
  -- renaming (Pointwise to All₂; map to map₂)
  hiding (refl; trans; sym)

data Ty : Set where
  bool int : Ty

open import GenericSyntax.Ctx Ty
open import GenericSyntax.Desc Ty

data `Hutton : Set where
  `val `add `leq `cond `let : `Hutton

binary : Ty → Ty → Ty → Desc
binary t₁ t₂ t = node 0 ([] ∷ [] ∷ []) λ { [] (t₁′ ∷ t₂′ ∷ []) t′ → t₁′ ≡ t₁ × t₂′ ≡ t₂ × t′ ≡ t }

op : List Ty → Ty → Desc
op ts t = node 0 (replicate []) λ { [] ts′ t′ → t′ ≡ t × Pointwise _≡_ ts′ (fromList ts) }

Hutton : Desc
Hutton = sg `Hutton λ
  { `val   → sg ℤ λ _ → node 0 []
             λ { [] [] t → t ≡ int }
  ; `add   → binary int int int
  ; `leq   → binary int int bool
  ; `cond  → node 0 ([] ∷ [] ∷ [] ∷ [])
             λ { [] (t₀ ∷ t₁ ∷ t₂ ∷ []) t → t₀ ≡ bool × t₁ ≡ t₂ × t ≡ t₁ }
  ; `let   → node 1 ((unbound ∷ []) ∷ (bound ∷ []) ∷ [])
             λ { (t₀ ∷ []) (t₀′ ∷ t′ ∷ []) t → t₀′ ≡ t₀ × t′ ≡ t }
  }

open import GenericSyntax.Repr Ty
open Typed Hutton

-- val : ∀ {Γ} → ℤ → Tm Γ int
pattern val c = con (sg `val (sg c (node [] [] {{refl}})))

-- add : ∀ {Γ} → Tm Γ int → Tm Γ int → Tm Γ int
pattern add x y = con (sg `add (node [] (x ∷ y ∷ []) {{refl , refl , refl}}))

-- leq : ∀ {Γ} → Tm Γ int → Tm Γ int → Tm Γ bool
pattern leq x y = con (sg `leq (node [] (x ∷ y ∷ []) {{refl , refl , refl}}))

-- cond : ∀ {Γ t} → Tm Γ bool → Tm Γ t → Tm Γ t → Tm Γ t
pattern cond b x y = con (sg `cond (node [] (b ∷ x ∷ y ∷ []) {{refl , (refl , refl)}}))

-- letH : ∀ {Γ t u} → Tm Γ t → Tm (Γ , t) u → Tm Γ u
pattern letH x y = con (sg `let (node (_ ∷ []) (x ∷ y ∷ []) {{ refl , refl }}))

rep : Ty → Set
rep int = ℤ
rep bool = Bool

eval : ∀ {Γ} → (Var Γ →̇ rep) → Tm Γ →̇ rep
eval env (var v)       = env v
eval env (val c)       = c
eval env (add x y)     = eval env x + eval env y
eval env (leq x y)     = ⌊ eval env y ≤? eval env x ⌋
eval env (cond b x y)  with eval env b
...                    | true   = eval env x
...                    | false  = eval env y
eval env (letH x y)    = let x′ = eval env x in eval (λ { vz → x′ ; (vs v) → env v }) y
