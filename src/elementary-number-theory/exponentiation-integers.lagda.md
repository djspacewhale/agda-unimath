# Exponentiation of integers by natural numbers

```agda
module elementary-number-theory.exponentiation-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.multiplication-integers
```

</details>

## Idea

[Exponentiation](elementary-number-theory.exponentiation-natural-numbers.md) of
an integer $m$ by a natural number $n$ is the number obtained by multiplying $m$
with itself $n$ times. It mirrors the definition for natural numbers, though
exponentiation by negative integers is more subtle and not addressed here.

## Definition

```agda
exp-ℤ : ℤ → ℕ → ℤ
exp-ℤ x zero-ℕ = one-ℤ
exp-ℤ x (succ-ℕ n) = exp-ℤ x n *ℤ x

infixr 50 _^ℤ_
_^ℤ_ = exp-ℤ
```
