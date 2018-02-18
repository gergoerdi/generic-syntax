module GenericSyntax.Examples.STLC.TypeCheck where

open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Vec.All using (_∷_; [])
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat

open import GenericSyntax.Examples.STLC.BoolChurch
import GenericSyntax.Repr
open GenericSyntax.Repr Ty using (size)
open GenericSyntax.Repr.Untype _ STLC
open GenericSyntax.Repr.Untyped _ STLC
open import GenericSyntax.Ctx Ty

▷-injₗ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t ≡ u
▷-injₗ refl = refl

▷-injᵣ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t′ ≡ u′
▷-injᵣ refl = refl

_≟ₜ_ : Decidable (_≡_ {A = Ty})
∙        ≟ₜ ∙          = yes refl
∙        ≟ₜ (_ ▷ _)    = no (λ ())
∙        ≟ₜ bool       = no (λ ())
(_ ▷ _)  ≟ₜ ∙          = no (λ ())
(t ▷ t′) ≟ₜ (u ▷ u′)   with t ≟ₜ u | t′ ≟ₜ u′
(t ▷ t′) ≟ₜ (.t ▷ .t′) | yes refl | yes refl = yes refl
(t ▷ t′) ≟ₜ (u ▷ u′)   | _ | no ¬p = no (¬p ∘ ▷-injᵣ)
(t ▷ t′) ≟ₜ (u ▷ u′)   | no ¬p | _ = no (¬p ∘ ▷-injₗ)
(_ ▷ _)  ≟ₜ bool       = no (λ ())
bool     ≟ₜ ∙          = no (λ ())
bool     ≟ₜ (u ▷ u₁)   = no (λ ())
bool     ≟ₜ bool       = yes refl

lookup : ∀ Γ → Fin (size Γ) → ∃ (Var Γ)
lookup ∅ ()
lookup (Γ , _) zero    = , vz
lookup (Γ , _) (suc v) = Data.Product.map _ vs (lookup Γ v)

lookup-correct : ∀ Γ v₀ → let (t , v) = lookup Γ v₀ in untype-var v ≡ v₀
lookup-correct ∅       ()
lookup-correct (Γ , t) zero     = refl
lookup-correct (Γ , t) (suc v₀) rewrite lookup-correct Γ v₀ = refl

module _ where
  pattern lam₀ t e = con (sg `lam (sg t (node (e ∷ []))))
  pattern _·₀_ f e = con (sg `app (node (f ∷ e ∷ [])))
  pattern true₀ = con (sg `true (node []))
  pattern false₀ = con (sg `false (node []))
  pattern if₀ b thn els = con (sg `if (node (b ∷ thn ∷ els ∷ [])))

open import Data.Maybe
open import Level renaming (zero to lzero)
open import Category.Monad
open RawMonad (Data.Maybe.monad {lzero})

typecheck : ∀ Γ → (e : Expr (size Γ)) → Maybe (∃ λ t → Σ (Tm Γ t) λ e′ → untype e′ ≡ e)
typecheck Γ (var v) = do
  let (t , v′) = lookup Γ v
  pure (t , var v′ , cong var (lookup-correct Γ v))
typecheck Γ (lam₀ t e) = do
  (_ , e′ , refl) ← typecheck (Γ , t) e
  pure (, lam t e′ , refl)
typecheck Γ (f ·₀ e) = do
  (u , e′ , refl) ← typecheck Γ e
  (u′ ▷ t , f′ , refl) ← typecheck Γ f
    where _ → nothing
  refl ← decToMaybe (u ≟ₜ u′)
  pure (, f′ · e′ , refl)
typecheck Γ true₀ = do
  pure (, true , refl)
typecheck Γ false₀ = do
  pure (, false , refl)
typecheck Γ (if₀ b thn els) = do
  (t₀ , b′ , refl) ← typecheck Γ b
  refl ← decToMaybe (t₀ ≟ₜ bool)
  (t , thn′ , refl) ← typecheck Γ thn
  (t′ , els′ , refl) ← typecheck Γ els
  refl ← decToMaybe (t ≟ₜ t′)
  pure (, if b′ thn′ els′ , refl)
