# The integers in the real numbers

```agda
module real-numbers.integer-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

Just as rational numbers [are real](real-numbers.rational-real-numbers.md), so
are the integers. They form a particularly nice subset of real numbers, as they
present in a sense the universal closed subgroup of `ℝ`.

## Definition

### The canonical map from `ℤ` to `ℝ`

```agda
real-ℤ : ℤ → ℝ lzero
real-ℤ = real-ℚ ∘ rational-ℤ
```
