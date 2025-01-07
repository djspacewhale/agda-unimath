# Strongly extensional maps

```agda
module foundation.strongly-extensional-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

Consider a function `f : A → B` between types equipped with apartness relations.
Then we say that `f` is **strongly extensional** if

```text
  f x # f y → x # y
```

## Definition

```agda
strongly-extensional :
  {l1 l2 l3 l4 : Level} (A : Type-With-Apartness l1 l2)
  (B : Type-With-Apartness l3 l4) →
  (type-Type-With-Apartness A → type-Type-With-Apartness B) → UU (l1 ⊔ l2 ⊔ l4)
strongly-extensional A B f =
  (x y : type-Type-With-Apartness A) →
  apart-Type-With-Apartness B (f x) (f y) → apart-Type-With-Apartness A x y
```

## Properties

### When `X Y` are sets, `f` being strongly extensional is a proposition

```agda
open import foundation.function-extensionality
open import foundation.propositional-extensionality

is-set-is-prop-strongly-extensional : {l1 l2 l3 l4 : Level} {X : Type-With-Apartness l1 l2} {Y : Type-With-Apartness l3 l4} (X-set : is-set (type-Type-With-Apartness X)) (Y-set : is-set (type-Type-With-Apartness Y)) (f : type-Type-With-Apartness X → type-Type-With-Apartness Y) → is-prop (strongly-extensional X Y f)
pr1 (is-set-is-prop-strongly-extensional {l1} {l2} {l3} {l4} {X} X-set Y-set f p q) = eq-htpy lem where
  lem : p ~ q
  lem x = eq-htpy lem2 where
    lem2 : p x ~ q x
    lem2 y = eq-htpy lem3 where
      lem3 : p x y ~ q x y
      lem3 z = lem4 (rel-apart-Type-With-Apartness X x y) (p x y z) (q x y z) where
        lem4 : {l : Level} (P : Prop l) (r s : type-Prop P) → r ＝ s
        lem4 P r s = eq-is-prop (pr2 P)
pr2 (is-set-is-prop-strongly-extensional X-set Y-set f p .p) refl = {!   !}
```
