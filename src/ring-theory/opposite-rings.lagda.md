# Opposite rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.opposite-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.transport-along-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets

open import group-theory.homomorphisms-abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

The opposite of a ring R is a ring with the same underlying abelian group, but
with multiplication given by `x·y := yx`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  op-Ring : Ring l
  pr1 op-Ring = ab-Ring R
  pr1 (pr1 (pr2 op-Ring)) = mul-Ring' R
  pr2 (pr1 (pr2 op-Ring)) x y z = inv (associative-mul-Ring R z y x)
  pr1 (pr1 (pr2 (pr2 op-Ring))) = one-Ring R
  pr1 (pr2 (pr1 (pr2 (pr2 op-Ring)))) = right-unit-law-mul-Ring R
  pr2 (pr2 (pr1 (pr2 (pr2 op-Ring)))) = left-unit-law-mul-Ring R
  pr1 (pr2 (pr2 (pr2 op-Ring))) x y z = right-distributive-mul-add-Ring R y z x
  pr2 (pr2 (pr2 (pr2 op-Ring))) x y z = left-distributive-mul-add-Ring R z x y
```

## Properties

### `op-Ring` is an [involution](foundation.involutions.md)

That is, `op-Ring (op-Ring R) ＝ R`.

```agda
module _
  {l : Level}
  where

  iso-ring-op-op-Ring : (R : Ring l) → iso-Ring (op-Ring (op-Ring R)) R
  pr1 (pr1 (iso-ring-op-op-Ring R)) = id-hom-Ab (ab-Ring R)
  pr2 (pr1 (iso-ring-op-op-Ring R)) = pair (λ {x} {x = x₁} → refl) refl
  pr2 (iso-ring-op-op-Ring R) = pair
    ((( λ z → z) , (λ {x} {x = x₁} → refl)) ,
    ( λ {x} {x = x₁} → refl) , refl)
    ( pair refl refl)

  is-involution-op-Ring : is-involution op-Ring
  is-involution-op-Ring R = eq-iso-Ring (op-Ring (op-Ring R)) R (iso-ring-op-op-Ring R)

  equiv-involution-op-Ring : Ring l ≃ Ring l
  pr1 equiv-involution-op-Ring = op-Ring
  pr2 equiv-involution-op-Ring = is-equiv-is-involution is-involution-op-Ring
```

### The canonical identification between `hom-Ring R S` and `hom-Ring (op-Ring R) (op-Ring S)`

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  open import foundation.univalence

  equiv-hom-Ring-op-Ring : hom-Ring R S ≃ hom-Ring (op-Ring R) (op-Ring S)
  pr1 (pr1 equiv-hom-Ring-op-Ring f) = hom-ab-hom-Ring R S f
  pr2 (pr1 equiv-hom-Ring-op-Ring f) = (λ {x} {x = x₁} → pr1 (pr2 f)) , pr2 (pr2 f)
  pr1 (pr1 (pr2 equiv-hom-Ring-op-Ring)) = λ z →
      pair (pr1 z) (pair (λ {x} {x = x₁} → pr1 (pr2 z)) (pr2 (pr2 z)))
  pr2 (pr1 (pr2 equiv-hom-Ring-op-Ring)) = λ x → refl
  pr1 (pr2 (pr2 equiv-hom-Ring-op-Ring)) = λ z →
    pair (pr1 z) (pair (λ {x} {x = x₁} → pr1 (pr2 z)) (pr2 (pr2 z)))
  pr2 (pr2 (pr2 equiv-hom-Ring-op-Ring)) = λ x → refl

  map-equiv-hom-Ring-op-Ring : hom-Ring R S → hom-Ring (op-Ring R) (op-Ring S)
  map-equiv-hom-Ring-op-Ring = map-equiv equiv-hom-Ring-op-Ring

  inv-map-equiv-hom-Ring-op-Ring : hom-Ring (op-Ring R) (op-Ring S) → hom-Ring R S
  inv-map-equiv-hom-Ring-op-Ring = map-equiv (inv-equiv equiv-hom-Ring-op-Ring)

  id-hom-Ring-op-Ring : hom-Ring R S ＝ hom-Ring (op-Ring R) (op-Ring S)
  id-hom-Ring-op-Ring = eq-equiv equiv-hom-Ring-op-Ring
```

### The canonical identification between `hom-Ring R (op-Ring S)` and `hom-Ring (op-Ring R) S`

This combines the previous two results and is useful for, say, proving
equivalence of left and right modules over commutative rings.

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  equiv-hom-Ring-to-op-Ring : hom-Ring R (op-Ring S) ≃ hom-Ring (op-Ring R) S
  equiv-hom-Ring-to-op-Ring = equiv-tr (λ T → hom-Ring (op-Ring R) T) (is-involution-op-Ring S) ∘e equiv-hom-Ring-op-Ring R (op-Ring S)
```
