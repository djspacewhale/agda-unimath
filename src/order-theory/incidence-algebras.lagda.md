# Incidence algebras

```agda
module order-theory.incidence-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.sets

open import linear-algebra.vectors-on-commutative-rings

open import order-theory.interval-subposets
open import order-theory.locally-finite-posets
open import order-theory.posets

open import ring-theory.algebras-rings
open import ring-theory.rings

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For a [locally finite poset](order-theory.locally-finite-posets.md) `P` and
[commutative ring](commutative-algebra.commutative-rings.md) `R`, there is a
canonical `R`-associative algebra whose underlying `R`-module are the set-maps
from the nonempty [intervals](order-theory.interval-subposets.md) of `P` to `R`
(which we constructify as the inhabited intervals), and whose multiplication is
given by a "convolution" of maps. This is the **incidence algebra** of `P` over
`R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {P : Poset l1 l2} (loc-fin : is-locally-finite-Poset P) (R : Commutative-Ring l3)
  where

  incidence-Ring : Commutative-Ring (l1 ⊔ l2 ⊔ l3)
  incidence-Ring = {!   !}

  inhabited-interval-map : UU (l1 ⊔ l2 ⊔ l3)
  inhabited-interval-map = {!   !}

  convolution : inhabited-interval-map → inhabited-interval-map → inhabited-interval-map
  convolution f g ((x , y), inhb) = {!   !}
```

## Special functions in the space of interval maps

```agda
  δ : inhabited-interval-map
  δ ((x , y) , inhb) = {!   !}

  ζ : inhabited-interval-map
  ζ x≤y = one-Commutative-Ring R
```

WIP: complete this definition after _R-modules_ have been defined. Defining
convolution of maps would be aided as well with a lemma on 'unordered' addition
in abelian groups over finite sets.
