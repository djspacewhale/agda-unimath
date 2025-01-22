# Modules over commutative rings

```agda
module commutative-algebra.modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.endomorphism-rings-abelian-groups

open import ring-theory.rings
open import ring-theory.homomorphisms-rings
open import ring-theory.modules-rings
open import ring-theory.opposite-rings
open import ring-theory.semirings
```

</details>

## Idea

When `R` is a _commutative_ ring, left and right `R`-modules coincide, and we
may simply discuss **modules** over `R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  R* : Ring l
  R* = ring-Commutative-Ring R

  left-mod-to-right-mod-CRing : {l2 : Level} → left-module-Ring l2 (R*) → right-module-Ring l2 (R*)
  pr1 (left-mod-to-right-mod-CRing M) = ab-left-module-Ring R* M
  pr1 (pr2 (left-mod-to-right-mod-CRing M)) = (map-hom-Ring R* (endomorphism-ring-ab-left-module-Ring R* M) (mul-hom-left-module-Ring R* M)) , lem where
    lem : preserves-mul-Semigroup (pr1 (pr1 (pr1 R*))) (pr1 (pr1 (ab-endomorphism-ring-Ab (pr1 M)))) (pr1 (pr1 (pr2 M)))
    lem {r} {s} = pr2 (pr1 (pr2 M))
  pr1 (pr2 (pr2 (left-mod-to-right-mod-CRing M))) {r} {s} = ap (pr1 (pr1 (pr2 M))) (commutative-mul-Commutative-Ring R r s) ∙ preserves-mul-hom-Ring R* (endomorphism-ring-ab-left-module-Ring R* M) (mul-hom-left-module-Ring R* M)
  pr2 (pr2 (pr2 (left-mod-to-right-mod-CRing M))) = pr2 (pr2 (pr2 M))
```
