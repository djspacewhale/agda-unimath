# Homotopy groups of pointed types

```agda
module synthetic-homotopy-theory.homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.iterating-functions
open import foundation.mere-equality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-truncations
open import foundation.truncations
open import foundation.universal-property-set-truncation
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.truncation-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

For nonzero natural numbers `n` and a pointed type `X`, the
[set-truncated](foundation.set-truncations.md)
[`n`-fold loop space](synthetic-homotopy-theory.iterated-loop-spaces.md) of `X`
has a canonical group structure; this is the `n`-th **homotopy group** of `X`.

## Definition

### The set of `n`-fold loops in `X`

```agda
module _
  {l : Level} (X : Pointed-Type l) (n : nonzero-ℕ)
  where

  iter-loop-set : Set l
  iter-loop-set = trunc-Set (type-Ω (iterated-loop-space (nat-nonzero-ℕ n) X))

  iter-loop-type : UU l
  iter-loop-type = type-Set (iter-loop-set)
```

### The operation on `n`-fold loops in the truncated loop space

```agda
module _
  {l : Level} (X : Pointed-Type l) (n : nonzero-ℕ)
  where

  iter-loop-mul : iter-loop-type X n → iter-loop-type X n → iter-loop-type X n
  iter-loop-mul f g = binary-map-trunc-Set (mul-Ω (iterated-loop-space (nat-nonzero-ℕ n) X)) f g
```

### `iter-loop-mul X n` endows the set `iter-loop-type X n` with a group structure

```agda
module _
  {l : Level} (X : Pointed-Type l) (n : nonzero-ℕ)
  where
```
