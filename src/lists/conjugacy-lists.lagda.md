# Conjugacy of lists

```agda
module lists.conjugacy-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.mere-equality
open import foundation.unit-type
open import foundation.universe-levels

open import foundation.empty-types

open import foundation-core.propositions

open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Given [lists](lists.lists.md) `u v` (over some `X`),
[concatening](lists.concatenation-lists.md) them is generally not commutative,
i.e. `uv ≠ vu`, but one would perhaps like a name for these sorts of pairs of
lists regardless. We could say that `uv` is
{{#concept "conjugate" Agda=is-conjugate-list}} to `vu`, but perhaps want to
define this relation on lists without having decompositions on hand from the
outset.

One approach is as follows: the empty list is conjugate to itself and to nothing
else, and two nonempty lists `u, v` are conjugate when there
[exists](foundation.existential-quantification.md) a list `z` with `uz`
[merely equal to](foundation.mere-equality.md) `zv`.

Note that conjugacy is weaker than commutativity - for example, `abc` is not
conjugate to `cba`.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  is-conjugate-list-Prop : Relation-Prop l (list X)
  is-conjugate-list-Prop nil nil = raise-unit-Prop l
  is-conjugate-list-Prop nil (cons x v) = raise-empty-Prop l
  is-conjugate-list-Prop (cons x u) nil = raise-empty-Prop l
  is-conjugate-list-Prop (cons x u) (cons y v) =
    ∃
      ( list X)
      ( λ w →
        mere-eq-Prop (concat-list (cons x u) w) (concat-list w (cons y v)))

  is-conjugate-list : Relation l (list X)
  is-conjugate-list u v = type-Prop (is-conjugate-list-Prop u v)

  conjugacy-class-list : list X → UU l
  conjugacy-class-list l = Σ (list X) (is-conjugate-list l)
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
- [Deciding Conjugacy of a Rational Relation](https://devmanuel.github.io/papers/dlt24.pdf)
