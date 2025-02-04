# Ideals of posets

```agda
module order-theory.ideals-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.ideals-preorders
open import order-theory.lower-types-posets
open import order-theory.lower-types-preorders
open import order-theory.preorders
open import order-theory.posets
```

</details>

## Idea

An **ideal** in a [poset](order-theory.posets.md) `P` is an ideal in the
underlying [preorder](order-theory.preorders.md) of `P`.

## Definitions

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-ideal-lower-type-Poset : {l3 : Level} (L : lower-type-Poset l3 P) → UU (l1 ⊔ l2 ⊔ l3)
  is-ideal-lower-type-Poset L = is-ideal-lower-type-Preorder (preorder-Poset P) L
```
