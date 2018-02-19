import GenericSyntax.Desc
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module GenericSyntax.ScopeCheck
  {Ty : Set} (desc : GenericSyntax.Desc.Desc Ty)
  {Name : Set} (_≟ₙ_ : Decidable (_≡_ {A = Name}))
  where

open GenericSyntax.Desc Ty
open import GenericSyntax.Repr Ty
module S = Untyped desc
module N = Unscoped desc Name
open S
open N renaming (Con to Conₙ)

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup; _++_)
open import Data.List hiding (_++_)
open import Data.Vec.All hiding (lookup)
open import Function
open import Relation.Nullary

Scope : ℕ → Set
Scope n = Vec Name n

bind : ∀ {n n′} → Scope n → Vec Name n′ → (bs : Vec Binder n′) → Scope (countV bs + n)
bind     Γ [] []             = Γ
bind {n} Γ (v ∷ vs) (bound ∷ bs)   = subst (Vec Name) (x+sy≡sx+y (countV bs) n) (bind (v ∷ Γ) vs bs)
bind     Γ (v ∷ vs) (unbound ∷ bs) = bind Γ vs bs

open import Data.Maybe

open import Level renaming (zero to lzero)
open import Category.Monad
open RawMonad (Data.Maybe.monad {lzero})

lookupName : ∀ {n} → Scope n → Name → Maybe (Fin n)
lookupName []       n  = nothing
lookupName (x ∷ Γ)  n  with x ≟ₙ n
lookupName (x ∷ Γ)  n  | no _      = Fin.suc <$> lookupName Γ n
lookupName (n ∷ Γ)  n  | yes refl  = pure zero

mutual
  resolveNames : ∀ {V} → Scope V → Form → Maybe (Expr V)
  resolveNames Γ (var v)  = var <$> lookupName Γ v
  resolveNames Γ (con c)  = con <$> resolveNames-con Γ c

  resolveNames-con : ∀ {c n} → Scope n → Conₙ c → Maybe (Con n c)
  resolveNames-con Γ (sg x c)      = sg x <$> resolveNames-con Γ c
  resolveNames-con Γ (node ns es)  = node <$> resolveNames⋆ Γ ns es

  resolveNames⋆ : ∀ {V n k} {sh : Shape n k} → Scope V → Vec Name n → N.Children k → Maybe (S.Children V sh)
  resolveNames⋆ {sh = []}      Γ ns  []        = pure []
  resolveNames⋆ {sh = bs ∷ _}  Γ ns  (e ∷ es)  = _∷_ <$> resolveNames (bind Γ ns bs) e ⊛ resolveNames⋆ Γ ns es

open import Data.Stream hiding (lookup; _++_)
open import Data.Product
open import Coinduction

splitStream : ∀ {a} {A : Set a} → (n : ℕ) → Stream A → Vec A n × Stream A
splitStream zero    xs       = [] , xs
splitStream (suc n) (x ∷ xs) with splitStream n (♭ xs)
splitStream (suc n) (x ∷ xs) | ys , ys′ = x ∷ ys , ys′

mutual
  addNames : ∀ {V} → Stream Name → Scope V → Expr V → Form
  addNames ss Γ (var v) = var (lookup v Γ)
  addNames ss Γ (con c) = con (addNames-con ss Γ c)

  addNames-con : ∀ {c V} → Stream Name → Scope V → Con V c → Conₙ c
  addNames-con ss Γ (sg x c)  = sg x (addNames-con ss Γ c)
  addNames-con ss Γ (node {n} es) with splitStream n ss
  addNames-con ss Γ (node {n} es) | ns , ss′ = node ns (addNames⋆ ss′ Γ ns es)

  addNames⋆ : ∀ {V n k} {sh : Shape n k} → Stream Name → Scope V → Vec Name n → S.Children V sh → N.Children k
  addNames⋆                ss Γ ns []        = []
  addNames⋆ {sh = bs ∷ _}  ss Γ ns (e ∷ es)  = addNames ss (bind Γ ns bs) e ∷ addNames⋆ ss Γ ns es

-- TODO: if `ns` is injective, then `addNames ns Γ` is the inverse of `resolveNames ∅ Γ`
