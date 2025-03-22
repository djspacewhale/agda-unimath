# Zero objects in precategories

```agda
module category-theory.zero-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.initial-objects-precategories
open import category-theory.precategories
open import category-theory.terminal-objects-precategories

open import foundation.conjunction
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A **zero object** in a [precategory](category-theory.precategories.md) `𝒞` is an
object that is both an initial and terminal object.

## Definitions

### The universal property of a zero object in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (x : obj-Precategory C)
  where

  is-zero-prop-obj-Precategory : Prop (l1 ⊔ l2)
  is-zero-prop-obj-Precategory = is-initial-prop-obj-Precategory C x ∧ is-terminal-prop-obj-Precategory C x

  is-zero-obj-Precategory : UU (l1 ⊔ l2)
  is-zero-obj-Precategory = type-Prop is-zero-prop-obj-Precategory

  is-prop-is-zero-obj-Precategory : is-prop is-zero-obj-Precategory
  is-prop-is-zero-obj-Precategory = is-prop-type-Prop is-zero-prop-obj-Precategory
```
