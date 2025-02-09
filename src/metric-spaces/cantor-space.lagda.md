# Cantor space

```agda
module metric-spaces.cantor-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The space of maps `ℕ → Fin 2` is canonically a premetric space, and is a metric
space when function extensionality (or even propositional extensionality) holds.
This we call {{#concept "Cantor space" Agda=Cantor-space}}.

```agda
module _ {l : Level} where
  Cantor-space : UU lzero
  Cantor-space = ℕ → Fin 2
```
