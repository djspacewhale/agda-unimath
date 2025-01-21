# Exponentiation of ring elements

```agda
module ring-theory.exponentiation-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

Exponentiation in a generic ring is similar to that in the
[ring of integers](elementary-number-theory.exponentiation-integers.md). We
define the general case here as it is important for, say, evaluation in
polynomial rings.

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  exp-Ring : type-Ring R → ℕ → type-Ring R
  exp-Ring r zero-ℕ = one-Ring R
  exp-Ring r (succ-ℕ n) = mul-Ring R (exp-Ring r n) r
```
