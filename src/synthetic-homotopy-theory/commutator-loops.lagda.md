# The commutator of loops

```agda

module synthetic-homotopy-theory.commutator-loops where

```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-types
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

For a [pointed type](structured-types.pointed-types.md) `A` and paths
`p q : Ω A` the **commutator** of `p` and `q` is the composite path
`p ∙ q ∙ p⁻¹ ∙ q⁻¹`.

## Definition

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  commutator-Ω : type-Ω A → type-Ω A → type-Ω A
  commutator-Ω p q = p ∙ (q ∙ (inv p ∙ inv q))
```
