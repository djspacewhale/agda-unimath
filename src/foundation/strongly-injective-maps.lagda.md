# Strongly injective maps

```agda
module foundation.strongly-injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.strongly-extensional-maps
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

For types `X Y : UU _`, a map `f : X → Y` is
[injective](foundation.injective-maps.md) when it creates equalities in an
appropriate sense. When they are equipped with tight apartness relations
`P : Tight-Apartness-Relation _ X, Q : Tight-Apartness-Relation _ Y` resp., `f`
is said to be **strongly injective** when it creates inequalities in the sense
of a section `strong-ext : (x y : X) → (x # y) → (f x # f y)`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) (ext : strongly-extensional (type-with-apartness-Type-With-Tight-Apartness X) (type-with-apartness-Type-With-Tight-Apartness Y) f)
  where

  strongly-injective : UU (l1 ⊔ l2 ⊔ l4)
  strongly-injective = (x y : type-Type-With-Tight-Apartness X) → apart-Type-With-Tight-Apartness X x y → apart-Type-With-Tight-Apartness Y (f x) (f y)
```

Note : although `ext` is not used in the definition above, strongly injective
maps are generally assumed to be strongly extensional beforehand, so we require
it in the context nonetheless.

## Properties

### Strongly injective maps are injective

As types with tight apartness relations are sets, they are in fact
[embeddings](foundation.embeddings.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) (ext : strongly-extensional (type-with-apartness-Type-With-Tight-Apartness X) (type-with-apartness-Type-With-Tight-Apartness Y) f) (p : strongly-injective X Y f ext)
  where

  strongly-injective-is-injective : is-injective f
  strongly-injective-is-injective {x} {y} γ = is-tight-apart-Type-With-Tight-Apartness X x y λ q → consistent-apart-Type-With-Tight-Apartness Y (f x) (f y) γ (p x y q)
```
