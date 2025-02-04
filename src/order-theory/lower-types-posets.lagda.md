# Lower types in posets

```agda
module order-theory.lower-types-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.propositions

open import order-theory.posets
open import order-theory.preorders
open import order-theory.lower-types-preorders
```

</details>

## Idea

A **lower type** in a poset `P` is a
[lower type](order-theory.lower-types-preorders.md) in the underlying
[preorder](order-theory.preorders.md) of `P`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-downwards-closed-subtype-Poset :
    {l3 : Level} (S : subtype l3 (type-Poset P)) → UU (l1 ⊔ l2 ⊔ l3)
  is-downwards-closed-subtype-Poset S = is-downwards-closed-subtype-Preorder (preorder-Poset P) S

lower-type-Poset : {l1 l2 : Level} (l3 : Level) → Poset l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
lower-type-Poset l3 P = Σ (subtype l3 (type-Poset P)) (is-downwards-closed-subtype-Poset P)
```
