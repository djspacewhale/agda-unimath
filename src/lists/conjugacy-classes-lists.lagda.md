# Conjugacy classes of lists

```agda
module lists.conjugacy-classes-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.sets
open import lists.lists
open import foundation-core.identity-types
open import lists.concatenation-lists
open import group-theory.concrete-groups
open import group-theory.concrete-group-actions
open import lists.permutation-lists
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.standard-cyclic-groups
open import group-theory.orbits-concrete-group-actions
```

</details>

## Idea

Let `A` be a type. Of the
[permutations on `list A`](lists.permutation-lists.md), notable are the
_rotations_, those from the natural subgroup `ℤ / n ⊂ S n` acting by rotating
lists. Elements in the total space of
`Σ ℕ (λ n → (ℤ / n ↻ Σ (list A) (λ l → length-list l ＝ n))`, the space of all
`ℤ/n`-actions on subtypes of lists of length `n`, are the **conjugacy classes**
of `list A`. Note that every list has a length, and so it is indeed sensible to
consider this directly as an "action" of `Σ ℕ (λ n → ℤ / n)` on `list A`.

The connected component of this total space at `l : list A` is equivalent to the
dependent product of tuples `u v : list A` and identifications
`p : l ＝ concat-list u v`. In that case, `concat-list v u` is a _conjugate_ of
`l`.

## Definition

```agda
module _
  {l : Level} (A : Set l)
  where

  conjugate-total-space-list : UU {!   !}
  conjugate-total-space-list = Σ ℕ (λ n → orbit-action-Concrete-Group {!   !} {!   !})
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
