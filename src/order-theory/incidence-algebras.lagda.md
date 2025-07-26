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

open import order-theory.finite-posets
open import order-theory.finite-preorders
open import order-theory.interval-subposets
open import order-theory.locally-finite-posets
open import order-theory.posets

open import ring-theory.algebras-rings
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
  incidence-Ab =
    function-Ab (ab-Commutative-Ring R) (inhabited-interval-Poset P)

  incidence-Module-CRing : Module-CRing (l1 ⊔ l2 ⊔ l3) R
  incidence-Module-CRing = {!   !}

  add-incidence-type-CRing :
    incidence-type-CRing → incidence-type-CRing → incidence-type-CRing
  add-incidence-type-CRing = add-Module-CRing R incidence-Module-CRing

  mul-hom-incidence-Module-CRing :
    hom-Ring (ring-Commutative-Ring R)
    ( endomorphism-ring-ab-left-module-Ring
    ( ring-Commutative-Ring R) incidence-Module-CRing)
  mul-hom-incidence-Module-CRing = mul-hom-Module-CRing R incidence-Module-CRing

  convolution-incidence-Module-CRing :
    incidence-type-CRing → incidence-type-CRing → incidence-type-CRing
  convolution-incidence-Module-CRing f g ((x , y) , _) =
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

  is-associative-convolution-incidence-Module-CRing :
    ( x y z : incidence-type-CRing) →
    convolution-incidence-Module-CRing x
      ( convolution-incidence-Module-CRing y z)
    ＝ convolution-incidence-Module-CRing
      ( convolution-incidence-Module-CRing x y) z
  is-associative-convolution-incidence-Module-CRing x y z = eq-htpy htpy
    where
    htpy :
      convolution-incidence-Module-CRing x
        ( convolution-incidence-Module-CRing y z) ~
      convolution-incidence-Module-CRing
        ( convolution-incidence-Module-CRing x y) z
    htpy ((a , b) , _) = {!   !}

  is-left-associative-action-convolution-incidence-Module-CRing :
    ( r : type-Commutative-Ring R) (x y : incidence-type-CRing) →
    {!   !} ＝ convolution-incidence-Module-CRing {!   !} y
  is-left-associative-action-convolution-incidence-Module-CRing r x y =
    eq-htpy {!   !}
    where
    htpy : {!   !} ~ convolution-incidence-Module-CRing {!   !} {!   !}
    htpy ((a , b) , _) = {!   !}

  is-right-associative-action-convolution-incidence-Module-CRing :
    ( r : type-Commutative-Ring R) (x y : incidence-type-CRing) →
    {!   !} ＝ convolution-incidence-Module-CRing x {!   !}
  is-right-associative-action-convolution-incidence-Module-CRing r x y =
    eq-htpy {!   !}
    where
    htpy : {!   !} ~ {!   !}
    htpy ((a , b) , _) = {!   !}

  is-left-distributive-convolution-incidence-Module-CRing :
    ( x y z : incidence-type-CRing) →
    convolution-incidence-Module-CRing {!   !} z ＝ {!   !}
  is-left-distributive-convolution-incidence-Module-CRing x y z = {!   !}

  is-right-distributive-convolution-incidence-Module-CRing :
    ( x y z : incidence-type-CRing) →
    convolution-incidence-Module-CRing x {!   !} ＝ {!   !}
  is-right-distributive-convolution-incidence-Module-CRing x y z =
    eq-htpy {!   !}
    where
    htpy : {!   !} ~ {!   !}
    htpy ((a , b) , _) = {!   !}

  incidence-algebra-Poset-CRing :
    Nonunital-Left-Algebra-Ring (l1 ⊔ l2 ⊔ l3) (ring-Commutative-Ring R)
  pr1 incidence-algebra-Poset-CRing = incidence-Module-CRing
  pr1 (pr2 incidence-algebra-Poset-CRing) =
    convolution-incidence-Module-CRing
  pr1 (pr2 (pr2 incidence-algebra-Poset-CRing)) =
    ( λ x y z → inv (is-associative-convolution-incidence-Module-CRing x y z))
  pr1 (pr1 (pr2 (pr2 (pr2 incidence-algebra-Poset-CRing)))) = {!   !}
  pr2 (pr1 (pr2 (pr2 (pr2 incidence-algebra-Poset-CRing)))) = {!   !}
  pr1 (pr2 (pr2 (pr2 (pr2 incidence-algebra-Poset-CRing)))) = {!   !}
  pr2 (pr2 (pr2 (pr2 (pr2 incidence-algebra-Poset-CRing)))) = {!   !}
```

WIP: complete this definition after _R-modules_ have been defined.
