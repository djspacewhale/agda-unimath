# Dependent products of left modules over a ring

```agda
module linear-algebra.dependent-products-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.dependent-products-abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.left-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

Given a family of (left `R`-)modules `Mᵢ` indexed by `i : I`, the dependent
product `Π(i : I), Mᵢ` is the left module consisting of dependent functions
assigning to each `i : I` an element of the underlying type of `Mᵢ`. The module
operations are given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : UU l2) (M : I → left-module-Ring l3 R)
  where

  Π-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  pr1 Π-left-module-Ring = Π-Ab I (λ i → ab-left-module-Ring R (M i))
  pr1 (pr1 (pr1 (pr2 Π-left-module-Ring)) r) x i = mul-left-module-Ring R (M i) r (x i)
  pr2 (pr1 (pr1 (pr2 Π-left-module-Ring)) r) {x} {y} = eq-htpy (λ x₁ → pr2 (pr1 (pr1 (pr2 (M x₁))) r))
  pr2 (pr1 (pr2 Π-left-module-Ring)) {r} {s} = {!   !}
  pr1 (pr2 (pr2 Π-left-module-Ring)) {r} {s} = {!   !}
  pr2 (pr2 (pr2 Π-left-module-Ring)) = {!   !}
```
