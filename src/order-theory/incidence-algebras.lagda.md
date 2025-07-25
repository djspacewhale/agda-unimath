# Incidence algebras

```agda
{-# OPTIONS --lossy-unification #-}

module order-theory.incidence-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.inhabited-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.semigroups

open import linear-algebra.left-modules-rings
open import linear-algebra.modules-commutative-rings

open import order-theory.finite-preorders
open import order-theory.finite-posets
open import order-theory.interval-subposets
open import order-theory.locally-finite-posets
open import order-theory.posets

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
open import ring-theory.semirings

open import univalent-combinatorics.finite-types
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
  {l1 l2 l3 : Level} (P : Poset l1 l2) (loc-fin : is-locally-finite-Poset P)
  (R : Commutative-Ring l3)
  where

  incidence-type-CRing : UU (l1 ⊔ l2 ⊔ l3)
  incidence-type-CRing = inhabited-interval-Poset P → type-Commutative-Ring R

  incidence-Ab : Ab (l1 ⊔ l2 ⊔ l3)
  incidence-Ab = function-Ab (ab-Commutative-Ring R) (inhabited-interval-Poset P)

  incidence-module-CRing : Module-CRing (l1 ⊔ l2 ⊔ l3) R
  incidence-module-CRing = {!   !}

  convolution-incidence-module-CRing :
    incidence-type-CRing → incidence-type-CRing → incidence-type-CRing
  convolution-incidence-module-CRing f g ((x , y) , inhb) =
    sum-finite-Commutative-Ring R
    ( finite-type-interval-locally-finite-Poset P loc-fin x y) conv
    where
    conv :
      type-Finite-Type (finite-type-interval-locally-finite-Poset P loc-fin x y)
      → type-Commutative-Ring R
    conv (z , x≤z , z≤y) =
      mul-Commutative-Ring R
      ( f ((x , z) , is-inhabited-lower-subinterval-Poset x≤z z≤y))
      ( g ((z , y) , is-inhabited-upper-subinterval-Poset x≤z z≤y))
```

WIP: complete this definition after _R-modules_ have been defined.
