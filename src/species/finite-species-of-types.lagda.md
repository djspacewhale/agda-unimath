# Finite species of types

```agda
module species.finite-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.propositions

open import species.species-of-types-in-subuniverses

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **finite species of types** is a map from `𝔽` to a universe. Note that this
definition differs from that of a
[species of finite types](species.species-of-finite-types.md) as the fibers are
not assumed to be finite.

## Definition

```agda
𝔽-species : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
𝔽-species l1 l2 = 𝔽 l1 → UU l2
```
