# Biproducts in precategories

```agda
module category-theory.biproducts-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coproducts-in-precategories
open import category-theory.precategories
open import category-theory.products-in-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.propositions
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

`C` **has finite biproducts** when there is a choice of biproduct for every pair
`x y : obj C`. This definition appears to conflict with existing library
definitions of having _binary_ (co)products, but in all cases it is in fact a
theorem that `C` has finite bi/co/products iff it has binary bi/co/products,
with a slick proof by induction and a natural associativity isomorphism (this
remains to be formalized).

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-biproduct-obj-Precategory : (x y b : obj-Precategory C) → hom-Precategory C b x → hom-Precategory C b y → hom-Precategory C x b → hom-Precategory C y b → UU (l1 ⊔ l2)
  is-biproduct-obj-Precategory x y b px py cx cy = is-product-obj-Precategory C x y b px py × is-coproduct-obj-Precategory C x y b cx cy

  biproduct-obj-Precategory : obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  biproduct-obj-Precategory x y = Σ (obj-Precategory C) λ b → Σ (hom-Precategory C b x) λ px → Σ (hom-Precategory C b y) λ py → Σ (hom-Precategory C x b) λ cx → Σ (hom-Precategory C y b) λ cy → is-biproduct-obj-Precategory x y b px py cx cy

  has-finite-biproducts-Precategory : UU (l1 ⊔ l2)
  has-finite-biproducts-Precategory = (x y : obj-Precategory C) → biproduct-obj-Precategory x y
```
