# Fermat's Little Theorem

```agda
module elementary-number-theory.fermat-little-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.exponentiation-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.identity-types
open import foundation.unit-type

open import foundation-core.coproduct-types
```

</details>

## Theorem

Fermat's Little Theorem states that for any prime number `p` and any integer
`a`, the number `a^p - a` is divisible by `p`. This is equivalent to the
statement that `a _^ℤ_ pred-prime-ℕ p` is congruent to 1 mod `p` for
`a : [1 , p-1]`. Eventually this module may collect several proofs, but for now
we formalize the proof by Euler at
[Wikipedia](https://en.wikipedia.org/wiki/Proofs_of_Fermat%27s_little_theorem#Multinomial_proofs).

```agda
fermat-little-theorem : (p : Prime-ℕ) → (a : ℤ) → div-ℤ (int-ℕ (nat-Prime-ℕ p)) (a ^ℤ nat-Prime-ℕ p -ℤ a)
fermat-little-theorem p a = {!   !}
```
