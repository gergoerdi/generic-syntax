Generic description of well-scoped, well-typed syntaxes
=======================================================

This repository contains Agda code for the paper "Generic description
The aim is a library that given a description of a language, will
deliver the following functionality to the user:

* A representation of syntactically valid, but not necessarily
  well-scoped formulas `Form : Set`

* A representation of well-scoped (but not necessarily well-typed)
  expressions `Expr : ℕ → Set` using de Bruijn indices to represent
  variables

* An intrinsically typed representation of well-typed, well-scoped
  terms `Tm : Ctx → Ty → Set`

* *All* the proofs about type-preserving renaming and simultaneous
  substitution over the typed representation

* A type erasure function `untype : Tm Γ t → Expr (size Γ)`

* A scope checker `resolveNames : Scope n → Form → Maybe (Expr n)`

As a validating example, a purely syntactic implementation of STLC is
included: reduction rules are explicit and defined in terms of
substitution, and normalization is proven a la the relevant chapter of
Pierce's Software Foundations.

Syntax definitions
------------------

A given language is described using the Agda datatype `Code`:

```
data Binder : Set where
  bound unbound : Binder

Shape : ℕ → ℕ → Set
Shape n k = Vec (Vec Binder n) k

data Desc : Set₁ where
  sg : (A : Set) (k: A → Desc) → Desc
  node : (n : ℕ) {k : ℕ} (shape : Shape n k) (wt : Vec Ty n → Vec Ty k → Ty → Set) → Desc
```

The only difference to https://gallais.github.io/pdf/draft_fscd17.pdf
is that the `node` constructor has a unified global view of all the
subterms; in particular, of all the types of the subterms. The meaning
of the well-typedness constraint `wt` is that it takes two collections
of types: the types of the `n` newly bound variables and the types of
the `k` subterms; it also receives the type of the term just being
constructed.

The idea behind `wt` is to encode the typing constraints the same way
as one encodes a GADT in Haskell using only existentials and type
equalities. Here, we use existentials for the types of subterms, and
allow arbitrary propositions for the constraints between them. The
typed representation for a given code carries witnesses of
well-typedness in their constructor for `node` (omitting some details
here):

```
data Con (Γ : Ctx) (t : Ty) : Desc → Set where
  sg : ∀ {A k} x → Con Γ t (k x) → Con Γ t (sg A k)
  node : ∀ {n k sh wt} (ts₀ : Vec Ty n) {ts : Vec Ty k} 
    (es : Children Γ ts₀ sh ts)
    {{_ : wt ts₀ ts t}} 
    → Con Γ t (node n sh wt)

Children : ∀ {n k} → Ctx → Vec Ty n → Shape n k → Vec Ty k → Set
Children Γ ts₀ = All₂ (λ bs → Tm (Γ <>< visible bs ts₀))

data Tm (Γ : Ctx) : Ty → Set where
  var : ∀ {t} → Var Γ t → Tm Γ t
  con : ∀ {t} → Con Γ t desc → Tm Γ t
```

STLC
----

The following example encodes STLC in Church-style:

```
data `STLC : Set where
  `lam `app : `STLC

STLC : Code
STLC = sg `STLC λ
  { `lam   → sg Ty λ t → node 1 ((bound ∷ []) ∷ []) λ { (t′ ∷ []) (u ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app   → node 0 ([] ∷ [] ∷ []) λ { [] (t₁ ∷ t₂ ∷ []) t → t₁ ≡ t₂ ▷ t }
  }
```

For ````lam```bda abstractions, we store an argument type, and then
bind one new variable, visible in one subterm; the well-typedness
constraint then requires the type of the newly bound variable to match
the user-supplied one, while also requiring the result type to be the
correct function type.

For function `app`lication, no new variables are bound in the two
subterms, so the well-typedness constraint only concerns the types of
subterms.

The following pattern synonyms illustrate the typed representation of
`STLC` (unfortunately, Agda doesn't support type signatures on pattern
synonyms, hence the comments):

```
-- lam : ∀ {Γ u} t → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern lam t e = con (sg `lam (sg t (node (_ ∷ []) (e ∷ []) {{refl , refl}})))

-- _·_ : ∀ {Γ u t} → Tm Γ (u ▷ t) → Tm Γ u → Tm Γ t
pattern _·_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))
```

If we want to add `let` to our language, that's expressible with the
following change to `STLC`:

```
data `STLC : Set where
  `lam `app `let : `STLC

STLC : Code
STLC = sg `STLC λ
  { `lam   → sg Ty λ t → node 1 ((bound ∷ []) ∷ [])
               λ { (t′ ∷ []) (u ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app   → node 0 ([] ∷ [] ∷ [])
               λ { [] (t₁ ∷ t₂ ∷ []) t → t₁ ≡ t₂ ▷ t }
  ; `let   →  node 1 ((unbound ∷ []) ∷ (bound ∷ []) ∷ [])
               λ { (t₀ ∷ []) (t₀′ ∷ t₁ ∷ []) t → t₀′ ≡ t₀ × t ≡ t₁ }
  }
```

In fact, we can easily implement a transformation that gets rid of
`let`s in some input language by turning them into `lam`bda applications:

```
data Phase : Set where
  input inlined : Phase

data `STLC : Phase → Set where
  `lam `app : ∀ {p} → `STLC p
  `let : `STLC input

STLC : Phase → Code
STLC p = sg (`STLC p) λ
  { `lam  → sg Ty λ t → node 1 ((bound ∷ []) ∷ []) λ 
               { (t′ ∷ []) (u ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app  → node 0 ([] ∷ [] ∷ []) λ 
               { [] (t₁ ∷ t₂ ∷ []) t → t₁ ≡ t₂ ▷ t }
  ; `let  → node 1 ((unbound ∷ []) ∷ (bound ∷ []) ∷ []) λ 
               { (t₀ ∷ []) (t₁ ∷ t₂ ∷ []) t → t₀ ≡ t₁ × t₂ ≡ t }
  }
  
open import SimplyTyped.Ctx Ty
open import SimplyTyped.Typed hiding (Tm)

Tm : (p : Phase) → Ctx → Ty → Set
Tm p = SimplyTyped.Typed.Tm (STLC p)

pattern lam t e = con (sg `lam (sg t (node (_ ∷ []) (e ∷ []) {{refl , refl}})))
pattern _·_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))
pattern letvar_in_ e₀ e = con (sg `let (node (_ ∷ []) (e₀ ∷ e ∷ []) {{refl , refl}}))

desugar ∶ ∀ {s φ Γ } → Tm φ s Γ → Tm desugared s Γ
desugar (var v)          = var v
desugar (f · e)          = desugar f · desugar e
desugar (lam t e)        = lam t (desugar e)
desugar (letvar e₀ in e) = lam _ (desugar e) · desugar e₀
```

We can also express `letrec` by simply making the newly-introduced variable
bound in both subterms:

```
  ; `letrec →  node 1 ((bound ∷ []) ∷ (bound ∷ []) ∷ [])
               λ { (t₀ ∷ []) (t₀′ ∷ t₁ ∷ []) t → t₀′ ≡ t₀ × t ≡ t₁ }
```

Of course, while adding the semantics of `letrec` is straightforward,
modifying the proof of strong normalization to cover this extended
language would be... tricky :)
