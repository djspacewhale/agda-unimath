# Homomorphisms of (left/right) `R`-modules

```agda
module ring-theory.homomorphisms-modules where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
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
  {l1 l2 : Level} {R : Ring l1} (M N : left-module-Ring l2 R)
  where

  is-linear-at-left : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) (r : type-Ring R) (x : type-left-module-Ring R M) → UU l2
  is-linear-at-left f r x = map-hom-Ab (pr1 M) (pr1 N) f (mul-left-module-Ring R M r x) ＝ mul-left-module-Ring R N r (map-hom-Ab (pr1 M) (pr1 N) f x)

  is-prop-is-linear-at-left : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) (r : type-Ring R) (x : type-left-module-Ring R M) → is-prop (is-linear-at-left f r x)
  is-prop-is-linear-at-left f r x = pr2 (Id-Prop (set-left-module-Ring R N) (map-hom-Ab (pr1 M) (pr1 N) f (mul-left-module-Ring R M r x)) (mul-left-module-Ring R N r (map-hom-Ab (pr1 M) (pr1 N) f x)))

  is-prop-is-linear-left-scalar : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) (r : type-Ring R) → is-prop ((x : type-left-module-Ring R M) → is-linear-at-left f r x)
  is-prop-is-linear-left-scalar f r = is-prop-Π (is-prop-is-linear-at-left f r)

  is-linear-left : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) → UU (l1 ⊔ l2)
  is-linear-left f = (r : type-Ring R) (x : type-left-module-Ring R M) → is-linear-at-left f r x

  is-prop-is-linear-left : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) → is-prop (is-linear-left f)
  is-prop-is-linear-left f = is-prop-Π (is-prop-is-linear-left-scalar f)

  prop-is-linear-left : (f : hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) → Prop (l1 ⊔ l2)
  prop-is-linear-left f = is-linear-left f , is-prop-is-linear-left f

  hom-set-left-module-Ring : Set (l1 ⊔ l2)
  hom-set-left-module-Ring = set-subset (hom-set-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R N)) λ f → prop-is-linear-left f

  hom-left-module-Ring : UU (l1 ⊔ l2)
  hom-left-module-Ring = type-Set hom-set-left-module-Ring

  map-hom-left-module-Ring : hom-left-module-Ring → type-left-module-Ring R M → type-left-module-Ring R N
  map-hom-left-module-Ring ((f , _) , _) x = f x
```
