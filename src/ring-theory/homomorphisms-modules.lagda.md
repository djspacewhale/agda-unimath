# Homomorphisms of (left/right) `R`-modules

```agda
module ring-theory.homomorphisms-modules where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.rings
open import ring-theory.modules-rings

```

</details>

## Idea

`R`-modules, like all algebraic structures, are famous for having homomorphisms
between them. A **homomorphism** of left `R`-modules
`M N : left-module-Ring _ R` is an `R`-linear homomorphism of underlying abelian
groups, that is, a map `f : type-left-module-Ring M → type-left-module-Ring N`
compatible with the respective additions and scalar multiplications, and
similarly for right modules.

## Definition

### Homomorphisms of left modules

```agda
module _
  {l1 l2 : Level} {R : Ring l1} (M N : left-module-Ring l2 R) (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N))
  where

  is-linear-at-left : (r : type-Ring R) (x : type-left-module-Ring R M) → UU l2
  is-linear-at-left r x = map-hom-Ab (pr1 M) (pr1 N) f (mul-left-module-Ring R M r x) ＝ mul-left-module-Ring R N r (map-hom-Ab (pr1 M) (pr1 N) f x)

  is-prop-is-linear-at-left : (r : type-Ring R) (x : type-left-module-Ring R M) → is-prop (is-linear-at-left r x)
  is-prop-is-linear-at-left r x = pr2 (Id-Prop (set-left-module-Ring R N) (map-hom-Ab (pr1 M) (pr1 N) f (mul-left-module-Ring R M r x)) (mul-left-module-Ring R N r (map-hom-Ab (pr1 M) (pr1 N) f x)))

  is-prop-is-linear-left-scalar : (r : type-Ring R) → is-prop ((x : type-left-module-Ring R M) → is-linear-at-left r x)
  is-prop-is-linear-left-scalar r = is-prop-Π (is-prop-is-linear-at-left r)

  is-linear-left : UU (l1 ⊔ l2)
  is-linear-left = (r : type-Ring R) (x : type-left-module-Ring R M) → is-linear-at-left r x

  is-prop-is-linear-left : is-prop (is-linear-left)
  is-prop-is-linear-left = is-prop-Π is-prop-is-linear-left-scalar
```
