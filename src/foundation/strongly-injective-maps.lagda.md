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

  is-strongly-injective : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) (f : type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) → {!   !} → UU {!   !}
  is-strongly-injective X Y f _ = (x y : type-Type-With-Tight-Apartness X) → apart-Type-With-Tight-Apartness X x y → apart-Type-With-Tight-Apartness Y (f x) (f y)

  Strong-Injection : (X : Type-With-Tight-Apartness l1 l2) (Y : Type-With-Tight-Apartness l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Strong-Injection X Y = Σ (type-Type-With-Tight-Apartness X → type-Type-With-Tight-Apartness Y) λ f → is-strongly-injective X Y f {!   !}
```

## Properties

### Strongly injective maps are injective

As types with tight apartness relations are sets, they are in fact
[embeddings](foundation.embeddings.md).

```agda
module _
  {l1 l2 l3 l4 : Level} {X : Type-With-Tight-Apartness l1 l2} {Y : Type-With-Tight-Apartness l3 l4} (f : Strong-Injection X Y) {p : strongly-extensional {!  X !} {! Y  !} {!   !}} (inj : is-strongly-injective X Y (pr1 f) {!  p !})
  where

  strongly-injective-is-injective : is-injective (pr1 f)
  strongly-injective-is-injective {x} {y} p = is-tight-apart-Type-With-Tight-Apartness X x y λ q → lem q where
    lem : ¬ apart-Type-With-Tight-Apartness X x y
    lem s = consistent-apart-Type-With-Tight-Apartness Y (pr1 f x) (pr1 f y) p lem2 where
      lem2 : apart-Type-With-Tight-Apartness Y (pr1 f x) (pr1 f y)
      lem2 = inj x y s
```
