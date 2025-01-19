# The Freshman's Dream

```agda
module elementary-number-theory.freshman-dream-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.binomial-theorem-integers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.exponentiation-integers

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

Freshmen often believe that `(a + b) ^ℤ n ＝ (a ^ℤ n) +ℤ (b ^ℤ n)` for all
`a b : ℤ, n : ℕ`. This is almost always false, but it is true mod `n` when `n`
is prime.

## Theorem

```agda
freshman-dream : (a b : ℤ) (p : ℕ) → is-prime-easy-ℕ p → cong-ℤ (int-ℕ p) ((a +ℤ b) ^ℤ p) (a ^ℤ p +ℤ b ^ℤ p)
freshman-dream a b p prime-p = {!   !}
```
