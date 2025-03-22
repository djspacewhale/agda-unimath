# Biproducts in precategories

```agda
module category-theory.biproducts-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coproducts-in-precategories
open import category-theory.products-in-precategories
```

</details>

## Idea

## Idea

A **biproduct** of objects `x y : obj C` in some precategory `C` consists of:

- an object `b`

- morphisms `px : hom C b x`, `py : hom C b y`, `cx : hom C x b`,
  `cy : hom C y b` such that

- (b , px , py) is a [product](category-theory.products-in-precategories.md) of
  `x` and `y`

- (b , cx , cy) is a [coproduct](category-theory.coproducts-in-precategories.md)
  of `x` and `y`

## Definitions
