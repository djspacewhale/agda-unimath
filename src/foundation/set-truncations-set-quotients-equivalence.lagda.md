# The canonical equivalence between the set truncation of `A` and the set quotient of `A` by mere equality

```agda
module foundation.set-truncations-set-quotients-equivalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.mere-equality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.set-truncations
open import foundation.uniqueness-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.sets
```

</details>

## Idea

The [set quotient](foundation.set-quotients.md) and
[set truncation](foundation.set-truncations) of a type `X` are canonically
equivalent, as they satisfy the same universal property.

```agda
module _
  {l : Level} (X : UU l)
  where

  equiv-set-truncation-set-quotient : type-trunc-Set X ≃ set-quotient (mere-eq-equivalence-relation X)
  equiv-set-truncation-set-quotient = equiv-uniqueness-set-quotient (mere-eq-equivalence-relation X) (trunc-Set X) (reflecting-map-mere-eq-unit-trunc-Set X) (is-set-quotient-trunc-Set X) (quotient-Set (mere-eq-equivalence-relation X)) (reflecting-map-quotient-map (mere-eq-equivalence-relation X)) (is-set-quotient-set-quotient (mere-eq-equivalence-relation X))

  map-equiv-set-truncation-set-quotient : type-trunc-Set X → set-quotient (mere-eq-equivalence-relation X)
  map-equiv-set-truncation-set-quotient = map-equiv equiv-set-truncation-set-quotient

  map-equiv-set-quotient-set-truncation : set-quotient (mere-eq-equivalence-relation X) → type-trunc-Set X
  map-equiv-set-quotient-set-truncation = map-inv-equiv equiv-set-truncation-set-quotient
```
