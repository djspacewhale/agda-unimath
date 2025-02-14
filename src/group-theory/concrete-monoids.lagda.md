# Concrete monoids

```agda
module group-theory.concrete-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes

open import group-theory.equivalences-group-actions
open import group-theory.cores-monoids
open import group-theory.groups
open import group-theory.group-actions
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-monoids
open import group-theory.monoids
open import group-theory.submonoids
open import group-theory.torsors
```

</details>

## Idea

A **concrete monoid**, or **univalent monoid**, is the homotopy type theoretic
analogue of [monoids](group-theory.monoids.md). We define it as a
[category](category-theory.categories.md) whose type of objects is
[pointed](structured-types.pointed-types.md) and
[connected](foundation.0-connected-types.md).

## Definition

```agda
is-concrete-monoid-Category : {l1 l2 : Level} → Category l1 l2 → UU l1
is-concrete-monoid-Category C = obj-Category C × is-0-connected (obj-Category C)

Concrete-Monoid : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Concrete-Monoid l1 l2 = Σ (Category l1 l2) (is-concrete-monoid-Category)

module _
  {l1 l2 : Level} (M : Concrete-Monoid l1 l2)
  where

  category-Concrete-Monoid : Category l1 l2
  category-Concrete-Monoid = pr1 M

  is-concrete-monoid-category-Concrete-Monoid :
    is-concrete-monoid-Category category-Concrete-Monoid
  is-concrete-monoid-category-Concrete-Monoid = pr2 M
```

## Properties

### Concrete monoids from monoids

Given a monoid, we can define its associated concrete monoid. The type of
objects is the [classifying type](group-theory.concrete-groups.md) of the
[core](group-theory.cores-monoids.md) of the monoid. Moreover, we must take care
in how we define the family of homomorphisms. They cannot simply be the constant
family, as [transporting along](foundation.transport-along-identifications.md)
an [invertible element](group-theory.invertible-elements-monoids.md) should
correspond to multiplying by the element in the family.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  M' : Group l
  M' = core-Monoid M

  obj-concrete-monoid-Monoid : UU (lsuc l)
  obj-concrete-monoid-Monoid = classifying-type-Group M'

  precategory-concrete-monoid-Monoid : Precategory (lsuc l) l
  pr1 precategory-concrete-monoid-Monoid = obj-concrete-monoid-Monoid
  pr1 (pr2 precategory-concrete-monoid-Monoid) _ _ = set-Monoid M
  pr1 (pr1 (pr2 (pr2 precategory-concrete-monoid-Monoid))) x y = mul-Monoid M x y
  pr1 (pr2 (pr1 (pr2 (pr2 precategory-concrete-monoid-Monoid))) x y z) = mul-Monoid M (mul-Monoid M x y) z
  pr2 (pr2 (pr1 (pr2 (pr2 precategory-concrete-monoid-Monoid))) x y z) = ((associative-mul-Monoid M x y z) , refl)
  pr1 (pr2 (pr2 (pr2 precategory-concrete-monoid-Monoid))) _ = unit-Monoid M
  pr1 (pr2 (pr2 (pr2 (pr2 precategory-concrete-monoid-Monoid)))) = left-unit-law-mul-Monoid M
  pr2 (pr2 (pr2 (pr2 (pr2 precategory-concrete-monoid-Monoid)))) = right-unit-law-mul-Monoid M

  equiv-torsor-from-iso : (X Y : obj-concrete-monoid-Monoid) → type-Group M' → equiv-Torsor-Group M' X Y
  pr1 (pr1 (equiv-torsor-from-iso ((X , X-act) , X-tor) ((Y , Y-act) , Y-tor) e)) = {!   !}
  pr2 (pr1 (equiv-torsor-from-iso X Y e)) = {!   !}
  pr2 (equiv-torsor-from-iso X Y e) g x = {!   !}

  category-concrete-monoid-Monoid : Category (lsuc l) l
  pr1 category-concrete-monoid-Monoid = precategory-concrete-monoid-Monoid
  pr1 (pr1 (pr2 category-concrete-monoid-Monoid X Y)) e = eq-equiv-Torsor-Group M' X Y (equiv-torsor-from-iso X Y e)
  pr2 (pr1 (pr2 category-concrete-monoid-Monoid X Y)) e = {!   !}
  pr1 (pr2 (pr2 category-concrete-monoid-Monoid X Y)) e = eq-equiv-Torsor-Group M' X Y (equiv-torsor-from-iso X Y e)
  pr2 (pr2 (pr2 category-concrete-monoid-Monoid X .X)) refl = {!   !}
```

The remainder of the construction remains to be written down. We note that this
is precisely the Rezk completion of the one object precategory associated to a
monoid.
