# Strongly injective maps

```agda
module foundation.strongly-injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.strongly-extensional-maps
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

For types `X Y : UU _`, a map `f : X → Y` is
[injective](foundation.injective-maps.md) when it creates equalities in an
appropriate sense. When they are equipped with tight apartness relations
`P : Tight-Apartness-Relation _ X, Q : Tight-Apartness-Relation _ Y` resp., a
[strongly extensional](foundation.strongly-extensional-maps.md) `f` is said to
be **strongly injective** when it creates inequalities in the sense of a section
`(x y : X) → (x # y) → (f x # f y)`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  strongly-injective : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) → strongly-extensional (type-with-apartness-Type-With-Tight-Apartness X) (type-with-apartness-Type-With-Tight-Apartness Y) f → UU (l1 ⊔ l2 ⊔ l4)
  strongly-injective X Y f _ = ((x y : type-Type-With-Tight-Apartness X) → apart-Type-With-Tight-Apartness X x y → apart-Type-With-Tight-Apartness Y (f x) (f y))

  Strong-Injection : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Strong-Injection X Y = Σ (type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) λ f → Σ (strongly-extensional (type-with-apartness-Type-With-Tight-Apartness X) (type-with-apartness-Type-With-Tight-Apartness Y) f) λ p → strongly-injective X Y f p

  map-Strong-Injection : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : Strong-Injection X Y) → type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y
  map-Strong-Injection X Y (f , p) x = f x

  is-strongly-extensional-Strong-Injection : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : Strong-Injection X Y) → strongly-extensional (type-with-apartness-Type-With-Tight-Apartness X) (type-with-apartness-Type-With-Tight-Apartness Y) (map-Strong-Injection X Y f)
  is-strongly-extensional-Strong-Injection X Y (f , p , q) = p

  is-strongly-injective-Strong-Injection : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : Strong-Injection X Y) → strongly-injective X Y (map-Strong-Injection X Y f) (is-strongly-extensional-Strong-Injection X Y f)
  is-strongly-injective-Strong-Injection X Y (f , p , q) = q
```

## Properties

### Strongly injective maps are injective

As types with tight apartness relations are sets, they are in fact
[embeddings](foundation.embeddings.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : Strong-Injection X Y)
  where

  f-inj : type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y
  f-inj = map-Strong-Injection X Y f

  strongly-injective-is-injective : is-injective f-inj
  strongly-injective-is-injective {x} {y} p = is-tight-apart-Type-With-Tight-Apartness X x y lem where
    lem : ¬ pr1 (rel-apart-Type-With-Tight-Apartness X x y)
    lem q = consistent-apart-Type-With-Tight-Apartness Y (f-inj x) (f-inj y) p (is-strongly-injective-Strong-Injection X Y f x y q)
```
