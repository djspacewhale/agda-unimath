# The Whitehead principle for maps

```agda
module synthetic-homotopy-theory.whitehead-principle-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.infinity-connected-maps
open import foundation.infinity-connected-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions

open import synthetic-homotopy-theory.whitehead-principle-types
```

</details>

## Idea

The {{#concept "Whitehead principle for maps" Agda=Whitehead-Principle-Map}}
asserts that [∞-connected maps](foundation.infinity-connected-maps.md) are
[equivalences](foundation-core.equivalences.md). I.e., if the
[fibers](foundation-core.fibers-of-maps.md) of a map `f : X → Y` are
[∞-connected](foundation.infinity-connected-types.md), then it is an
equivalence. This principle is also referred to as _hypercompleteness_ and is
not validated in every ∞-topos.

## Definition

```agda
Whitehead-Principle-Map-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Whitehead-Principle-Map-Level l1 l2 =
  ( X : UU l1) → (Y : UU l2) → (f : X → Y) → is-∞-connected-map f → is-equiv f

Whitehead-Principle-Map : UUω
Whitehead-Principle-Map = {l1 l2 : Level} → Whitehead-Principle-Map-Level l1 l2
```

## Properties

### The Whitehead principle for maps implies the Whitehead principle for types

```agda
Whitehead-Principle-Maps-implies-Types :
  Whitehead-Principle-Map → Whitehead-Principle
Whitehead-Principle-Maps-implies-Types WP X is-∞-conn-X =
  is-contr-equiv-unit eq
  where
    eq : X ≃ unit
    pr1 eq = terminal-map X
    pr2 eq =
      WP X unit (terminal-map X)
        ( λ x → is-∞-connected-equiv
          ( equiv-fiber-terminal-map star) is-∞-conn-X)
```

### The Whitehead principle for types implies the Whitehead principle for maps

```agda
Whitehead-Principle-Types-implies-Maps :
  Whitehead-Principle → Whitehead-Principle-Map
Whitehead-Principle-Types-implies-Maps WP X Y f is-∞-conn-f =
  is-equiv-is-contr-map is-contr-map-f
  where
    is-contr-map-f : is-contr-map f
    is-contr-map-f y = WP (fiber f y) (λ x → is-∞-conn-f y x)
```

## External links

- [hypercomplete object](https://ncatlab.org/nlab/show/hypercomplete+object) on
  $n$Lab
- [Whitehead theorem](https://en.m.wikipedia.org/w/index.php?title=Whitehead_theorem)
  on Wikipedia

## References

For the equivalent concept in the ∞-categorical semantics of homotopy type
theory, cf. §6.5.2 of Lurie's _Higher Topos Theory_ {{#cite Lurie09}}.

{{#bibliography}}
