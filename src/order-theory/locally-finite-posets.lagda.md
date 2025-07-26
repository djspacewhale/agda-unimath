# Locally finite posets

```agda
{-# OPTIONS --lossy-unification #-}

module order-theory.locally-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets

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

  type-interval-locally-finite-Poset : (x y : type-Poset X) → UU (l1 ⊔ l2)
  type-interval-locally-finite-Poset x y =
    type-Finite-Type (finite-type-interval-locally-finite-Poset x y)

  is-finite-interval-locally-finite-Poset :
    (x y : type-Poset X) → is-finite (type-interval-locally-finite-Poset x y)
  is-finite-interval-locally-finite-Poset x y =
    is-finite-type-Finite-Type (finite-type-interval-locally-finite-Poset x y)
```

## Properties

### Locally finite posets have decidable equality

This is essentially because their intervals have a decidable order relation.
When `x y : type-Poset P`, decide if `[x , y] , [y , x]` are both inhabited, and
observe that `x ＝ y` iff both of these intervals are inhabited.

```agda
module _
  {l1 l2 : Level} {P : Poset l1 l2}
  where

  both-intervals-are-inhabited-is-eq-Poset :
    (x y : type-Poset P) → x ＝ y →
    (is-inhabited-interval P x y × is-inhabited-interval P y x)
  pr1 (both-intervals-are-inhabited-is-eq-Poset x x refl) = unit-trunc-Prop
    ( pair x (pair (pr1 (pr2 (pr2 (pr1 P))) x) (pr1 (pr2 (pr2 (pr1 P))) x)))
  pr2 (both-intervals-are-inhabited-is-eq-Poset x x refl) = unit-trunc-Prop
    ( pair x (pair (pr1 (pr2 (pr2 (pr1 P))) x) (pr1 (pr2 (pr2 (pr1 P))) x)))

  is-eq-both-intervals-are-inhabited-Poset :
    (x y : type-Poset P) →
    (is-inhabited-interval P x y × is-inhabited-interval P y x) → x ＝ y
  is-eq-both-intervals-are-inhabited-Poset x y (x≤y , y≤x) =
    antisymmetric-leq-Poset P x y
      ( is-le-is-inhabited-interval-Poset P x y x≤y)
      ( is-le-is-inhabited-interval-Poset P y x y≤x)

  equiv-is-eq-both-intervals-are-inhabited-Poset :
    (x y : type-Poset P) →
    ((x ＝ y) ≃ ((is-inhabited-interval P x y) × (is-inhabited-interval P y x)))
  pr1 (equiv-is-eq-both-intervals-are-inhabited-Poset x y) =
    both-intervals-are-inhabited-is-eq-Poset x y
  pr1 (pr1 (pr2 (equiv-is-eq-both-intervals-are-inhabited-Poset x y))) =
    is-eq-both-intervals-are-inhabited-Poset x y
  pr2 (pr1 (pr2 (equiv-is-eq-both-intervals-are-inhabited-Poset x y))) p =
    eq-is-prop (is-prop-product
      ( is-property-is-inhabited (pr1 (pr1 (poset-interval-Subposet P x y))))
      ( is-property-is-inhabited (pr1 (pr1 (poset-interval-Subposet P y x)))))
  pr1 (pr2 (pr2 (equiv-is-eq-both-intervals-are-inhabited-Poset x y))) =
    is-eq-both-intervals-are-inhabited-Poset x y
  pr2 (pr2 (pr2 (equiv-is-eq-both-intervals-are-inhabited-Poset x y))) p =
    is-set-has-uip (is-set-type-Poset P) x y
      (( pr1 (pr2 (pr2 (equiv-is-eq-both-intervals-are-inhabited-Poset x y)))
      ∘ pr1 (equiv-is-eq-both-intervals-are-inhabited-Poset x y)) p) p

module _
  {l1 l2 : Level} (P : Poset l1 l2) (loc-fin : is-locally-finite-Poset P)
  where

  has-decidable-equality-is-locally-finite-Poset :
    has-decidable-equality (type-Poset P)
  has-decidable-equality-is-locally-finite-Poset x y =
    is-decidable-equiv (equiv-is-eq-both-intervals-are-inhabited-Poset x y)
      ( is-decidable-product
        ( is-decidable-type-trunc-Prop-is-finite
          ( is-finite-interval-locally-finite-Poset P loc-fin x y))
        ( is-decidable-type-trunc-Prop-is-finite
          ( is-finite-interval-locally-finite-Poset P loc-fin y x)))
```
