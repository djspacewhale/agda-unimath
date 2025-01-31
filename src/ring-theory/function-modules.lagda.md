# Function modules

```agda
module ring-theory.function-modules where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.sets
open import foundation-core.propositions

open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.modules-rings
open import ring-theory.rings
```

</details>

## Idea

The mapping space `X → type-Ring R` for a ring `R` and a type `X` is canonically
a (left/right) module over `R`. The module operations are defined pointwise, and
this satisfies a universal property.

## Definitions

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (X : UU l2)
  where

  left-action-function-left-module-Ring : hom-Ring R (endomorphism-ring-Ab (function-Ab (pr1 R) X))
  pr1 left-action-function-left-module-Ring = {!   !}
  pr2 left-action-function-left-module-Ring = {!   !}

  function-left-module-Ring : left-module-Ring {!   !} R
  function-left-module-Ring = (function-Ab (ab-Ring R) X) , {!   !}
```
