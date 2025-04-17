# Semiadditive categories

```agda
module category-theory.semiadditive-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.biproducts-in-precategories
open import category-theory.precategories
open import category-theory.zero-objects-precategories

open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import group-theory.commutative-monoids
```

</details>

## Idea

A [precategory](category-theory.precategories.md) is **semiadditive** when it
has a [zero object](category-theory.zero-objects-precategories.md) and admits
binary (hence finite)
[biproducts](category-theory.biproducts-in-precategories.md).

Such precategories are interesting as their hom-sets admit a canonical
[commutative monoid](group-theory.commutative-monoids.md) structure.

## Definition

```agda
is-semiadditive-Precategory : {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
is-semiadditive-Precategory C = has-zero-object-Precategory C × has-finite-biproducts-Precategory C
```

## Properties

### The commutative monoid structure on hom sets

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (semiadditive : is-semiadditive-Precategory C)
  where
```
