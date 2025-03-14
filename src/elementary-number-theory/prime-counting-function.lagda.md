# The prime counting function

```agda
module elementary-number-theory.prime-counting-function where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.initial-segments-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.dependent-pair-types

open import foundation-core.decidable-propositions

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Primality of natural numbers is decidable, and decidable subtypes of finite
types (say, finite initial segments of ℕ) have a count; thus, we may define the
**prime counting function** `π : ℕ → ℕ` mapping `n` to the number of prime
numbers in `0 1 ... n`.

## Definition

```agda
π : ℕ → ℕ
π n = number-of-elements-subset-Finite-Type {!   !} λ m → is-prime-ℕ-Decidable-Prop {!   !}
```
