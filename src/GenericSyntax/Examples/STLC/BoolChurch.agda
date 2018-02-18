module GenericSyntax.Examples.STLC.BoolChurch where

open import Data.Nat
open import Data.Fin using (Fin)
open import Relation.Nullary
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec
open import Data.Vec.Relation.InductivePointwise using ([]; _∷_)

infixr 20 _▷_

data Ty : Set where
  ∙    :  Ty
  _▷_  :  Ty → Ty → Ty
  bool :  Ty

open import GenericSyntax.Desc Ty
open import GenericSyntax.Repr Ty

data `STLC : Set where
  `app `lam `true `false `if : `STLC

STLC : Desc
STLC = sg `STLC λ
  { `app    →  node 0 ([] ∷ [] ∷ []) λ { [] (t₁ ∷ t₂ ∷ []) t₀                    → t₁ ≡ t₂ ▷ t₀ }
  ; `lam    →  sg Ty λ t → node 1 ((bound ∷ []) ∷ []) λ { (t′ ∷ []) (u ∷ []) t₀  → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `true   →  node 0 [] λ { [] [] t₀                                            → t₀ ≡ bool }
  ; `false  →  node 0 [] λ { [] [] t₀                                            → t₀ ≡ bool }
  ; `if     →  node 0 ([] ∷ [] ∷ [] ∷ []) λ { [] (b ∷ t₁ ∷ t₂ ∷ []) t₀           → b ≡ bool × t₁ ≡ t₀ × t₂ ≡ t₀ }
  }

open Typed STLC public

-- _·_ : ∀ {Γ t u} → Tm Γ (t ▷ u) → Tm Γ t → Tm Γ u
pattern _·_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))

-- lam : ∀ {Γ u} t → Tm _ u → Tm Γ (t ▷ u)
pattern lam t e = con (sg `lam (sg t (node (_ ∷ []) (e ∷ []) {{refl , refl}})))

pattern true = con (sg `true (node [] [] {{refl}}))
pattern false = con (sg `false (node [] [] {{refl}}))
pattern if b thn els = con (sg `if (node [] (b ∷ thn ∷ els ∷ []) {{refl , refl , refl}}))
