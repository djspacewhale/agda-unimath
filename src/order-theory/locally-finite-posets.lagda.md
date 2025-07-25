# Locally finite posets

```agda
module order-theory.locally-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions

open import order-theory.finite-posets
open import order-theory.finite-preorders
open import order-theory.interval-subposets
open import order-theory.posets

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A poset `X` is said to be **locally finite** if for every `x, y ∈ X`, the
[interval subposet](order-theory.interval-subposets.md) `[x, y]` consisting of
`z : X` such that `x ≤ z ≤ y`, is finite.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-locally-finite-Poset-Prop : Prop (l1 ⊔ l2)
  is-locally-finite-Poset-Prop =
    Π-Prop
      ( type-Poset X)
      ( λ x →
        Π-Prop
          ( type-Poset X)
          ( λ y →
            is-finite-Poset-Prop (poset-interval-Subposet X x y)))

  is-locally-finite-Poset : UU (l1 ⊔ l2)
  is-locally-finite-Poset = type-Prop is-locally-finite-Poset-Prop

  is-prop-is-locally-finite-Poset : is-prop is-locally-finite-Poset
  is-prop-is-locally-finite-Poset =
    is-prop-type-Prop is-locally-finite-Poset-Prop
```

### The finite poset of an interval in a locally finite poset

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (X-loc-fin : is-locally-finite-Poset X)
  where

  finite-interval-subposet-locally-finite-Poset' :
    ( x y : type-Poset X) → Finite-Poset' (l1 ⊔ l2) l2
  pr1 (finite-interval-subposet-locally-finite-Poset' x y) =
    poset-interval-Subposet X x y
  pr2 (finite-interval-subposet-locally-finite-Poset' x y) =
    X-loc-fin x y

  finite-interval-subposet-locally-finite-Poset :
    ( x y : type-Poset X) → Finite-Poset (l1 ⊔ l2) l2
  finite-interval-subposet-locally-finite-Poset x y =
    Finite-Poset'-to-Finite-Poset (l1 ⊔ l2) l2
    ( finite-interval-subposet-locally-finite-Poset' x y)

  finite-type-interval-locally-finite-Poset :
    ( x y : type-Poset X) → Finite-Type (l1 ⊔ l2)
  finite-type-interval-locally-finite-Poset x y =
    finite-type-Finite-Poset (finite-interval-subposet-locally-finite-Poset x y)
```
