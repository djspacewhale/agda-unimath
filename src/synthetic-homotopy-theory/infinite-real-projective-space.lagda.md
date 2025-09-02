# The infinite dimensional real projective space

```agda
module synthetic-homotopy-theory.infinite-real-projective-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.standard-cyclic-groups

open import foundation.connected-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.equality-coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.propositional-truncations
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.sections
open import foundation-core.retractions
open import foundation-core.equivalences
open import foundation-core.empty-types
open import foundation-core.identity-types

open import group-theory.concrete-groups
open import group-theory.symmetric-concrete-groups
open import group-theory.groups

open import higher-group-theory.eilenberg-mac-lane-spaces

open import structured-types.equivalences-h-spaces
open import structured-types.pointed-types
open import structured-types.pointed-equivalences

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "infinite dimensional real projective space" Agda=ℝP∞}} `ℝP∞` is
the classifying space of the
[symmetric group](group-theory.symmetric-concrete-groups.md) on a
[two-element type](univalent-combinatorics.2-element-types.md).

## Definitions

### As the delooping of a two-element type

```agda
ℝP∞ : UU (lsuc lzero)
ℝP∞ = classifying-type-symmetric-Concrete-Group (Fin-Set 2)

concrete-group-ℝP∞ : Concrete-Group (lsuc lzero)
concrete-group-ℝP∞ = symmetric-Concrete-Group (Fin-Set 2)

point-ℝP∞ : ℝP∞
point-ℝP∞ = shape-symmetric-Concrete-Group (Fin-Set 2)

pointed-type-ℝP∞ : Pointed-Type (lsuc lzero)
pr1 pointed-type-ℝP∞ = ℝP∞
pr2 pointed-type-ℝP∞ = point-ℝP∞
```

### As the sequential colimit of the finite dimensional real projective spaces

The infinite dimensional real projective space `ℝP∞` may be realized as a
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of finite
dimensional real projective spaces, see Section IV {{#cite BR17}}.

```text
  ℝP⁻¹ ──→ ℝP⁰ ──→ ℝP¹ ──→ ℝP² ──→ ⋯ ──→ ℝPⁿ ──→ ℝPⁿ⁺¹ ──→ ⋯ ──→ ℝP∞
```

> This remains to be formalized.

## Properties

### `ℝP∞` is a [`K(ℤ/2,1)`](higher-group-theory.eilenberg-mac-lane-spaces.md)

```agda
map-ℤ-Mod-2-ℝP∞ : Fin 2 → type-Ω (iterated-loop-space 0 pointed-type-ℝP∞)
map-ℤ-Mod-2-ℝP∞ (inl (inr star)) = refl
map-ℤ-Mod-2-ℝP∞ (inr star) =
  eq-equiv-classifying-type-symmetric-Concrete-Group
    ( Fin-Set 2)
    ( Fin-Set 2 , unit-trunc-Prop refl)
    ( Fin-Set 2 , unit-trunc-Prop refl)
    ( swap-2-Element-Type fin-2-Element-Type)

map-ℝP∞-ℤ-Mod-2 : type-Ω (iterated-loop-space 0 pointed-type-ℝP∞) → Fin 2
map-ℝP∞-ℤ-Mod-2 X = {!   !}

equiv-ℤ-Mod-2-ℝP∞ : Fin 2 ≃ type-Ω (iterated-loop-space 0 pointed-type-ℝP∞)
pr1 equiv-ℤ-Mod-2-ℝP∞ = map-ℤ-Mod-2-ℝP∞
pr1 (pr1 (pr2 equiv-ℤ-Mod-2-ℝP∞)) = map-ℝP∞-ℤ-Mod-2
pr2 (pr1 (pr2 equiv-ℤ-Mod-2-ℝP∞)) = {!   !}
pr1 (pr2 (pr2 equiv-ℤ-Mod-2-ℝP∞)) = map-ℝP∞-ℤ-Mod-2
pr2 (pr2 (pr2 equiv-ℤ-Mod-2-ℝP∞)) = {!   !}

pointed-equiv-ℤ-Mod-2-ℝP∞ :
  pointed-type-Group (ℤ-Mod-Group 2) ≃∗
  Ω (iterated-loop-space 0 pointed-type-ℝP∞)
pr1 pointed-equiv-ℤ-Mod-2-ℝP∞ = equiv-ℤ-Mod-2-ℝP∞
pr2 pointed-equiv-ℤ-Mod-2-ℝP∞ = refl

is-eilenberg-mac-lane-space-ℝP∞ :
  is-eilenberg-mac-lane-space-Group (ℤ-Mod-Group 2) 1 pointed-type-ℝP∞
pr1 is-eilenberg-mac-lane-space-ℝP∞ =
  is-0-connected-classifying-type-Concrete-Group concrete-group-ℝP∞
pr1 (pr2 is-eilenberg-mac-lane-space-ℝP∞) = pointed-equiv-ℤ-Mod-2-ℝP∞
pr2 (pr2 is-eilenberg-mac-lane-space-ℝP∞) = {!   !}
```

## References

{{#bibliography}}

## See also

- [The infinite dimensional complex projective space](synthetic-homotopy-theory.infinite-complex-projective-space.md)
