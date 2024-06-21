# Symmetric bundles

```agda
module operads.symmetric-bundle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-components-universes
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.identity-types

open import group-theory.automorphism-groups
open import group-theory.symmetric-concrete-groups

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **generic symmetric bundle** is the ℕ-bundle of
[symmetric concrete groups](group-theory.symmetric-concrete-groups) of
[standard finite types](univalent-combinatorics.standard-finite-types), notated
Sym. A **symmetric bundle** (at universe level l) is a function Sym → Set l. By
chasing universal properties, this is an ℕ-indexed family of types together with
actions of each $S_n$ on the $n$-th type. Most cases will focus on set-bundles.

```agda
Sym : UU (lsuc lzero)
Sym = Σ ℕ (λ n → classifying-type-symmetric-Concrete-Group (Fin-Set n))

symmetric-bundle : (l : Level) → UU (lsuc l)
symmetric-bundle l = Sym → UU l

symmetric-bundle-sets : (l : Level) → UU (lsuc l)
symmetric-bundle-sets l = Sym → Set l
```
