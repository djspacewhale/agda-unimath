# Terms over signatures

```agda
module universal-algebra.terms-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.sets

open import lists.concatenation-lists
open import lists.functoriality-tuples
open import lists.lists
open import lists.lists-discrete-types
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

A {{#concept "term" disambiguation="in a signature" Agda=Term}} is an abstract
representation of a well formed expression which uses only variables and
operations in the signature. Terms may take values in any
[set](foundation-core.sets.md) (this condition is to ensure the type of terms
over `X`, say, is a set). When `X = ℕ`, we often call these **de Bruijn
variables**, which are especially useful for defining
[equational theories](universal-algebra.algebraic-theories.md).

## Definitions

### Terms

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (X : Set l2)
  where

  data Term : UU (l1 ⊔ l2) where
    var-Term : type-Set X → Term
    op-Term : is-model σ Term

  variables-term : Term → list (type-Set X)

  variables-term-tuple : {n : ℕ} → tuple Term n → list (type-Set X)

  variables-term (var-Term x) = cons x nil
  variables-term (op-Term f x) = variables-term-tuple x

  variables-term-tuple empty-tuple = nil
  variables-term-tuple (x ∷ v) =
    concat-list (variables-term x) (variables-term-tuple v)

  arity-term : Term → ℕ
  arity-term t = length-list (variables-term t)
```

### Assignment of variables

An assignment of variables assigns each de Bruijn variable to an element in a
type.

```agda
  assignment : {l3 : Level} → (A : UU l3) → UU (l2 ⊔ l3)
  assignment A = type-Set X → A
```

### Evaluation of terms

Given a model of a type `A` and an assignment of variables, any term can be
evaluated to a concrete element of the type `A`.

```agda
  eval-term :
    {l2 : Level} → {A : UU l2} →
    is-model σ A → assignment A → Term → A

  eval-tuple :
    {l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model σ A → assignment A → tuple Term n → tuple A n

  eval-term m assign (var-Term x) = assign x
  eval-term m assign (op-Term f x) = m f (eval-tuple m assign x)

  eval-tuple m assign empty-tuple = empty-tuple
  eval-tuple m assign (x ∷ v) =
    eval-term m assign x ∷ (eval-tuple m assign v)

  eval-tuple-map-tuple-eval-term :
    {l2 : Level} {A : UU l2} {n : ℕ} →
    (m : is-model σ A) → (assign : assignment A) → (v : tuple Term n) →
    eval-tuple m assign v ＝ map-tuple (eval-term m assign) v
  eval-tuple-map-tuple-eval-term m assign empty-tuple = refl
  eval-tuple-map-tuple-eval-term m assign (x ∷ v) =
    ap (eval-term m assign x ∷_) (eval-tuple-map-tuple-eval-term m assign v)
```

### Evaluation for constant terms

If a term `t` uses no variables, then any model on a type `A` assigns `t` to an
element of `A`.

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (X : Set l2)
  where

  eval-constant-term :
    {l3 : Level} {A : UU l3} →
    (is-model σ A) →
    (t : Term σ X) →
    (variables-term σ X t ＝ nil) →
    A

  eval-constant-term-tuple :
    {l3 : Level} {A : UU l3} {n : ℕ} →
    (is-model σ A) →
    (v : tuple (Term σ X) n) →
    (all-tuple (λ t → is-nil-list (variables-term σ X t)) v) →
    tuple A n

  eval-constant-term m (op-Term f x) p =
    m f (eval-constant-term-tuple m x {!   !})

  eval-constant-term-tuple m empty-tuple p = empty-tuple
  eval-constant-term-tuple m (x ∷ v) (p , p') =
    eval-constant-term m x p ∷ eval-constant-term-tuple m v p'
```

### The induced function by a de Bruijn term on a model

```agda
de-bruijn-Term : {l : Level} (σ : signature l) → UU l
de-bruijn-Term σ = Term σ ℕ-Set

module _
  {l : Level} (σ : signature l)
  where

  de-bruijn-variables-term : de-bruijn-Term σ → list ℕ
  de-bruijn-variables-term = variables-term σ ℕ-Set

  de-bruijn-variables-term-tuple : {n : ℕ} → tuple (de-bruijn-Term σ) n → list ℕ
  de-bruijn-variables-term-tuple = variables-term-tuple σ ℕ-Set

  de-bruijn-assignment : {l2 : Level} (A : UU l2) → UU l2
  de-bruijn-assignment A = assignment σ ℕ-Set A

  arity-de-bruijn-term : de-bruijn-Term σ → ℕ
  arity-de-bruijn-term x = arity-term σ ℕ-Set x

module _
  {l1 : Level} (σ : signature l1)
  where

  tuple-assignment :
    {l2 : Level} {A : UU l2} →
    ℕ → (l : list ℕ) →
    tuple A (succ-ℕ (length-list l)) →
    de-bruijn-assignment σ A
  tuple-assignment x nil (y ∷ empty-tuple) n = y
  tuple-assignment x (cons x' l) (y ∷ y' ∷ v) n
    with
    ( has-decidable-equality-ℕ x n)
  ... | inl p = y
  ... | inr p = tuple-assignment x' l (y' ∷ v) n

  induced-function-term :
    {l2 : Level} {A : UU l2} →
    is-model σ A →
    (t : de-bruijn-Term σ) →
    tuple A (arity-de-bruijn-term σ t) → A
  induced-function-term {l2} {A} m t v with
    ( has-decidable-equality-list
      has-decidable-equality-ℕ
      (de-bruijn-variables-term σ t) nil)
  ... | inl p = eval-constant-term σ ℕ-Set m t p
  ... | inr p = {!   !}


  assignment-tuple :
    {l2 : Level} {A : UU l2} →
    (l : list ℕ) →
    de-bruijn-assignment σ A →
    tuple A (length-list l)
  assignment-tuple nil f = empty-tuple
  assignment-tuple (cons x l) f = (f x) ∷ (assignment-tuple l f)
```

### Translation of terms

```agda
translation-term :
  {l1 l2 l3 : Level} →
  (σ : signature l1) →
  (τ : signature l2) →
  is-extension-signature σ τ →
  (X : Set l3) →
  Term τ X → Term σ X

translation-tuple :
  {l1 l2 l3 : Level} →
  (σ : signature l1) →
  (τ : signature l2) →
  {n : ℕ} →
  is-extension-signature σ τ →
  (X : Set l3) →
  tuple (Term τ X) n → tuple (Term σ X) n

translation-term σ τ ext X (var-Term x) = var-Term x
translation-term σ τ ext X (op-Term f v) =
  op-Term
    ( emb-extension-signature σ τ ext f)
    ( tr
      ( tuple (Term σ X))
      ( arity-preserved-extension-signature σ τ ext f)
      ( translation-tuple σ τ ext X v))

translation-tuple σ τ ext X empty-tuple = empty-tuple
translation-tuple σ τ ext X (x ∷ v) =
  ( translation-term σ τ ext X x) ∷
  ( translation-tuple σ τ ext X v)
```
