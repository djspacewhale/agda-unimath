# Algebras over commutative rings

```agda
module commutative-algebra.algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.sets

open import ring-theory.central-elements-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

When `R` is a _commutative_ ring, (unital) `R`-algebras admit a nice definition
as rings `A` (possibly noncommutative) equipped with a ring homomorphism
`R → Z A` (the center of `A`).

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  ring-hom-is-in-center : {l2 : Level} (A : Ring l2) → hom-Ring (ring-Commutative-Ring R) A → UU (l ⊔ l2)
  ring-hom-is-in-center A f = (x : type-Commutative-Ring R) → is-central-element-Ring A (map-hom-Ring (ring-Commutative-Ring R) A f x)

  central-hom-Ring : (l2 : Level) → Ring l2 → UU (l ⊔ l2)
  central-hom-Ring l2 A = Σ (hom-Ring (ring-Commutative-Ring R) A) (λ f → ring-hom-is-in-center A f)

  Algebra-Commutative-Ring : (l2 : Level) → UU (l ⊔ lsuc l2)
  Algebra-Commutative-Ring l2 = Σ (Ring l2) λ A → central-hom-Ring l2 A
```
