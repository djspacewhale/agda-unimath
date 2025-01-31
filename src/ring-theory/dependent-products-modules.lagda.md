# Dependent products of modules

```agda
module ring-theory.dependent-products-modules where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.equivalences

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.rings
open import ring-theory.homomorphisms-rings
open import ring-theory.semirings
open import ring-theory.modules-rings
```

</details>

## Idea

Given a family of (left/right) `R`-modules `M i` indexed by `i : I`, their
dependent product `Π(i:I), M i` is again a (left/right) `R`-module.

## Definition

### Dependent products of left modules

```agda
module _
  {l1 l2 l3 : Level} {R : Ring l1} (I : UU l2) (M : I → left-module-Ring l3 R)
  where

  ab-left-module-Π-Ring : Ab (l2 ⊔ l3)
  ab-left-module-Π-Ring = Π-Ab I (λ i → ab-left-module-Ring R (M i))

  ab-left-module-Π-Ring-action : hom-Ring R (endomorphism-ring-Ab ab-left-module-Π-Ring)
  pr1 (pr1 (pr1 ab-left-module-Π-Ring-action) r) x i = mul-left-module-Ring R (M i) r (x i)
  pr2 (pr1 (pr1 ab-left-module-Π-Ring-action) r) {x} {y} = {!   !}
  pr2 (pr1 ab-left-module-Π-Ring-action) {r} {s} = {!   !}
  pr1 (pr2 ab-left-module-Π-Ring-action) {r} {s} = {!   !}
  pr2 (pr2 ab-left-module-Π-Ring-action) = {!   !}

  left-module-Π-Ring : left-module-Ring (l2 ⊔ l3) R
  pr1 left-module-Π-Ring = ab-left-module-Π-Ring
  pr2 left-module-Π-Ring = ab-left-module-Π-Ring-action
```
