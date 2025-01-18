# The (concrete) Mathieu groups

```agda
module finite-group-theory.mathieu-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.universe-levels

open import group-theory.concrete-groups

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.steiner-systems
```

</details>

## Idea

The **Mathieu groups** were the earliest finite simple groups studied. Four of
them are automorphism groups of Steiner systems and the fifth is an index-2
subgroup of one of the others.

## Definition

### The Mathieu group `M-12`

```agda
S-5-6-12 : Steiner-System 5 6 12
S-5-6-12 = {!   !}
```
