# Central elements of rings

```agda
module ring-theory.central-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-locale-of-propositions
open import foundation.propositions
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.injective-maps
open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.large-frames
open import order-theory.large-posets
open import order-theory.large-preorders

open import ring-theory.central-elements-semirings
open import ring-theory.rings
open import ring-theory.subrings
open import ring-theory.subsets-rings
```

</details>

## Idea

An element `x` of a ring `R` is said to be central if `xy ＝ yx` for every
`y : R`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-ring-Prop : type-Ring R → Prop l
  is-central-element-ring-Prop =
    is-central-element-semiring-Prop (semiring-Ring R)

  is-central-element-Ring : type-Ring R → UU l
  is-central-element-Ring = is-central-element-Semiring (semiring-Ring R)

  is-prop-is-central-element-Ring :
    (x : type-Ring R) → is-prop (is-central-element-Ring x)
  is-prop-is-central-element-Ring =
    is-prop-is-central-element-Semiring (semiring-Ring R)
```

## Properties

### The zero element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-zero-Ring : is-central-element-Ring R (zero-Ring R)
  is-central-element-zero-Ring =
    is-central-element-zero-Semiring (semiring-Ring R)
```

### The unit element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-one-Ring : is-central-element-Ring R (one-Ring R)
  is-central-element-one-Ring =
    is-central-element-one-Semiring (semiring-Ring R)
```

### The sum of two central elements is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-add-Ring :
    (x y : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R y → is-central-element-Ring R (add-Ring R x y)
  is-central-element-add-Ring =
    is-central-element-add-Semiring (semiring-Ring R)
```

### The negative of a central element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-neg-Ring :
    (x : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R (neg-Ring R x)
  is-central-element-neg-Ring x H y =
    ( left-negative-law-mul-Ring R x y) ∙
    ( ( ap (neg-Ring R) (H y)) ∙
      ( inv (right-negative-law-mul-Ring R y x)))
```

### `-1` is a central element

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-neg-one-Ring :
    is-central-element-Ring R (neg-one-Ring R)
  is-central-element-neg-one-Ring =
    is-central-element-neg-Ring R (one-Ring R) (is-central-element-one-Ring R)
```

### The product of two central elements is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-mul-Ring :
    (x y : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R y → is-central-element-Ring R (mul-Ring R x y)
  is-central-element-mul-Ring =
    is-central-element-mul-Semiring (semiring-Ring R)
```

### The center of `R` is a subring of `R`

This remains a work in progress.

```agda
module _
  {l : Level} (R : Ring l)
  where

  center-subtype : subset-Ring l R
  center-subtype = λ r → is-central-element-ring-Prop R r

  ring-center : UU l
  ring-center = type-subset-Ring R center-subtype

  center-inclusion : ring-center → type-Ring R
  center-inclusion = inclusion-subset-Ring R center-subtype

  center-injection : injection ring-center (type-Ring R)
  center-injection = injection-subset-Ring R center-subtype

  is-injective-center-inclusion : is-injective center-inclusion
  is-injective-center-inclusion = pr2 center-injection

  ring-center-is-set : is-set ring-center
  ring-center-is-set =
    is-set-is-injective (is-set-type-Ring R) is-injective-center-inclusion

  center-Set : Set l
  center-Set = ring-center , ring-center-is-set
```
