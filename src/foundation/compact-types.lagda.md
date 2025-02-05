# Compact types

```agda
module foundation.compact-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.decidable-types
```

</details>

## Idea

[Martin Escardó](https://martinescardo.github.io/papers/compact-ordinals-Types-2019-abstract.pdf)
defines a type `X` to be **compact** if the type `Σ X (λ x → p x ＝ true)` is
[decidable](foundation.decidable-types.md) for every `p : X → bool`, cf.
[the booleans](foundation.booleans.md).

## Definition

```agda

```
