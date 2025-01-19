# Freshman's dream for rings

```agda
module ring-theory.freshman-dream-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types

open import ring-theory.binomial-theorem-rings
open import ring-theory.characteristics-rings
open import ring-theory.rings
```

## Idea

In general, `(a + b) ^ n ≠ a ^ n + b ^ n` for `a b : type-Ring R, n : ℕ`.
However, when `n` is prime and `R` has characteristic `n`, it holds; this is
often humorously known as the **Freshman's Dream**.

## Theorem

```agda

```
