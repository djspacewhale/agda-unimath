# Interval subposets

```agda
module order-theory.interval-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.subtypes

open import order-theory.posets
open import order-theory.subposets
```

</details>

## Idea

Given two elements `x` and `y` in a poset `X`, the **interval subposet**
`[x , y]` is the subposet of `X` consisting of all elements `z` in `X` such that
`x ≤ z` and `z ≤ y`. Note that interval subposets need not be linearly ordered.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (x y : type-Poset X)
  where

  is-in-interval-Poset : (z : type-Poset X) → Prop l2
  is-in-interval-Poset z =
    product-Prop (leq-prop-Poset X x z) (leq-prop-Poset X z y)

  poset-interval-Subposet : Poset (l1 ⊔ l2) l2
  poset-interval-Subposet = poset-Subposet X is-in-interval-Poset
```

### The predicate of an interval being inhabited

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (x y : type-Poset X)
  where

  is-inhabited-interval : UU (l1 ⊔ l2)
  is-inhabited-interval =
    is-inhabited (type-Poset (poset-interval-Subposet X x y))

  is-prop-is-inhabited-interval : is-prop is-inhabited-interval
  is-prop-is-inhabited-interval =
    is-property-is-inhabited (pr1 (pr1 (poset-interval-Subposet X x y)))

  is-inhabited-interval-Prop : Prop (l1 ⊔ l2)
  pr1 is-inhabited-interval-Prop = is-inhabited-interval
  pr2 is-inhabited-interval-Prop = is-prop-is-inhabited-interval
```

### The type of inhabited intervals of a poset

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  inhabited-interval-subtype-Poset :
    subtype (l1 ⊔ l2) (type-Poset X × type-Poset X)
  inhabited-interval-subtype-Poset (x , y) = is-inhabited-interval-Prop X x y

  inhabited-interval-Poset : UU (l1 ⊔ l2)
  inhabited-interval-Poset = type-subtype inhabited-interval-subtype-Poset
```

### For `x ≤ z ≤ y`, the intervals `[x , z]` and `[z , y]` are both inhabited

```agda
module _
  {l1 l2 : Level} {P : Poset l1 l2} {x y z : type-Poset P}
  (x≤z : leq-Poset P x z) (z≤y : leq-Poset P z y)
  where

  is-inhabited-lower-subinterval-Poset : is-inhabited-interval P x z
  is-inhabited-lower-subinterval-Poset =
    unit-trunc-Prop (pair x (pair (pr1 (pr2 (pr2 (pr1 P))) x) x≤z))

  is-inhabited-upper-subinterval-Poset : is-inhabited-interval P z y
  is-inhabited-upper-subinterval-Poset =
    unit-trunc-Prop (pair z (pair (pr1 (pr2 (pr2 (pr1 P))) z) z≤y))
```
