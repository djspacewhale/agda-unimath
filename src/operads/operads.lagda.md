# Operads

```agda
module operads.operads where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.transport-along-identifications

open import operads.symmetric-bundle
```

</details>

## Idea

An **operad** (of sets) is a
[symmetric bundle of sets](operads.symmetric-bundle) $F$ together with a
designated element $i : F(1)$ and for each $k : ℕ$ and family
$n : (x : Fin k) → ℕ$ a composition
$F(k) × ((x : Fin k) → F (n x)) → F (∑ (n x))$ satisfying some axioms.

```agda
module _
  {l : Level} (F : symmetric-bundle-sets l)
  where
```
