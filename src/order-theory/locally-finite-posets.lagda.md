# Locally finite posets

```agda
module order-theory.locally-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.identity-types

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

### The finite set of an interval in a locally finite poset

```agda
module _
  {l1 l2 : Level} {X : Poset l1 l2} (loc-fin : is-locally-finite-Poset X)
  where

  interval-locally-finite-Poset : (x y : type-Poset X) → Poset (l1 ⊔ l2) l2
  interval-locally-finite-Poset x y = poset-interval-Subposet X x y

  interval-locally-finite-Poset-𝔽 : (x y : type-Poset X) → 𝔽 (l1 ⊔ l2)
  interval-locally-finite-Poset-𝔽 x y = (type-Poset (interval-locally-finite-Poset x y)) , (pr1 (loc-fin x y))
```

## Properties

### Locally finite posets have decidable equality

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (loc-fin : is-locally-finite-Poset X)
  where
```
