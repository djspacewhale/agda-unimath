# (Symmetric) operads

```agda

module operads.operads where

```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Operads** are gadgets that formalize the idea of a family of `n`-ary
operations on an object in a symmetric monoidal category. In this module, we
define operads - what some in the literature call _symmetric_ operads - in
0-types as [structured](foundation.structured-types.md) set-bundles of
[standard finite types](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
set-bundle-Fin : (l : Level) → UU (lsuc l)
set-bundle-Fin l = 𝔽 l → Set l

module _
  {l : Level} (O : set-bundle-Fin l)
  where
```
