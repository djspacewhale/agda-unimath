# Configuration spaces

```agda
module structured-types.configuration-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.apartness-relations
open import foundation.strongly-injective-maps
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

## Idea

For a type `X` with a
[tight apartness relation](foundation.apartness-relations.md) `_#_`, the
**`n`'th ordered configuration space** of `X` is, equivalently, the type of
[strongly injective maps](foundation.strongly-injective-maps) from `Fin n` to
`X`.

## Definition

```agda
Conf : {l1 l2 : Level} (n : ℕ) (X : Type-With-Tight-Apartness l1 l2) → UU (l1 ⊔ l2)
Conf n X = Strong-Injection (Fin-Type-With-Tight-Apartness n) X
```
