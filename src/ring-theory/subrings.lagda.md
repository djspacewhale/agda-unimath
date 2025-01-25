# Subrings

```agda
module ring-theory.subrings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.unital-binary-operations

open import foundation-core.cartesian-product-types
open import foundation.identity-types
open import foundation-core.subtypes

open import group-theory.abelian-groups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subgroups-abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A **subring** of a [ring](ring-theory.rings.md) `R` is an additive subgroup `S`
of `R` that has 1 and is closed under multiplication.

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-subring-subset-Ring : {l2 : Level} (S : subset-Ring l2 R) → UU (l ⊔ l2)
  is-subring-subset-Ring S = contains-one-subset-Ring R S × is-closed-under-multiplication-subset-Ring R S × is-additive-subgroup-subset-Ring R S

  Subring-Ring : (l2 : Level) → UU (l ⊔ lsuc l2)
  Subring-Ring l2 = Σ (subset-Ring l2 R) λ S → is-subring-subset-Ring S

  ring-Subring-Ring : {l2 : Level} → Subring-Ring l2 → Ring (l ⊔ l2)
  pr1 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)) = ab-Subgroup-Ab (ab-Ring R) (S , S-subgroup-add)
  pr1 (pr1 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) (x , x-subset) (y , y-subset) = (mul-Ring R x y) , (S-closed-mul x y x-subset y-subset)
  pr2 (pr1 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) x y z = eq-type-subtype S (R .pr2 .pr1 .pr2 (x .pr1) (y .pr1) (z .pr1))
  pr1 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr1 .pr1 = pr1 (pr1 (R .pr2 .pr2))
  pr1 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr1 .pr2 = S-has-one
  pr1 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr2 .pr1 x = eq-type-subtype S (left-unit-law-mul-Ring R (pr1 x))
  pr1 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr2 .pr2 x = eq-type-subtype S (right-unit-law-mul-Ring R (pr1 x))
  pr2 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr1 a b c = eq-type-subtype S (R .pr2 .pr2 .pr2 .pr1 (a .pr1) (pr1 b) (pr1 c))
  pr2 (pr2 (pr2 (ring-Subring-Ring (S , S-has-one , S-closed-mul , S-subgroup-add)))) .pr2 a b c = eq-type-subtype S (R .pr2 .pr2 .pr2 .pr2 (pr1 a) (pr1 b) (c .pr1))
```
