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
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where
```
