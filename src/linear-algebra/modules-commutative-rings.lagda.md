# Modules over commutative rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.endomorphism-rings-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.right-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.opposite-rings
open import ring-theory.rings
```

</details>

## Idea

When a [ring](ring-theory.rings.md) `R` is
[commutative](commutative-algebra.commutative-rings.md), its
[left](linear-algebra.left-modules-rings.md) and
[right](linear-algebra.right-modules-rings.md) modules agree with each other,
and we may speak simply of **modules** over `R`. For this proof to remain
predicative, we restrict the equivalence to left/right `R`-modules of a fixed
[universe level](foundation.universe-levels.md).

The convention is to take left modules to be simply **modules**.

## Proof

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  private
    R* : Ring l
    R* = ring-Commutative-Ring R

  left-mod-to-right-mod-CRing :
    {l2 : Level} → left-module-Ring l2 (R*) → right-module-Ring l2 (R*)
  pr1 (left-mod-to-right-mod-CRing M) = ab-left-module-Ring R* M
  pr2 (left-mod-to-right-mod-CRing {l2} M) =
    map-hom-Ring-CRing-op-Ring R (endomorphism-ring-ab-left-module-Ring R* M)
    ( mul-hom-left-module-Ring R* M)

  right-mod-to-left-mod-CRing :
    {l2 : Level} → right-module-Ring l2 (R*) → left-module-Ring l2 (R*)
  pr1 (right-mod-to-left-mod-CRing M) = ab-right-module-Ring R* M
  pr2 (right-mod-to-left-mod-CRing {l2} M) =
    inv-map-hom-Ring-CRing-op-Ring R
    ( endomorphism-ring-ab-right-module-Ring R* M)
    ( mul-hom-right-module-Ring R* M)

  left-mod-right-mod-CRing-equiv :
    {l2 : Level} → left-module-Ring l2 (R*) ≃ right-module-Ring l2 (R*)
  pr1 left-mod-right-mod-CRing-equiv = left-mod-to-right-mod-CRing
  pr1 (pr1 (pr2 left-mod-right-mod-CRing-equiv)) = right-mod-to-left-mod-CRing
  pr2 (pr1 (pr2 left-mod-right-mod-CRing-equiv)) (M , M-mul) =
    eq-pair-Σ refl lem
    where
    lem :
      dependent-identification
      ( λ A → hom-Ring R* (op-Ring (endomorphism-ring-Ab A))) refl (pr2
      ( left-mod-to-right-mod-CRing
      ( pr1 (pr1 (pr2 left-mod-right-mod-CRing-equiv)) (M , M-mul)))) M-mul
    lem =
      is-section-map-inv-is-equiv
      ( is-equiv-map-hom-Ring-CRing-op-Ring R (endomorphism-ring-Ab M)) M-mul
  pr1 (pr2 (pr2 left-mod-right-mod-CRing-equiv)) = right-mod-to-left-mod-CRing
  pr2 (pr2 (pr2 left-mod-right-mod-CRing-equiv)) (M , M-mul) =
    eq-pair-Σ refl lem
    where
    lem :
      dependent-identification
      ( λ A → hom-Ring R* (endomorphism-ring-Ab A)) refl (pr2
      ( right-mod-to-left-mod-CRing
      ( pr1 left-mod-right-mod-CRing-equiv (M , M-mul)))) M-mul
    lem =
      is-retraction-map-section-is-equiv
      ( is-equiv-map-hom-Ring-CRing-op-Ring R (endomorphism-ring-Ab M)) M-mul
```

## Modules over a commutative ring

```agda
Module-CRing :
  {l1 : Level} (l2 : Level) (R : Commutative-Ring l1) → UU (l1 ⊔ lsuc l2)
Module-CRing l2 R = left-module-Ring l2 (ring-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (M : Module-CRing l2 R)
  where

  ab-Module-CRing : Ab l2
  ab-Module-CRing = pr1 M

  set-Module-CRing : Set l2
  set-Module-CRing = set-Ab ab-Module-CRing

  type-Module-CRing : UU l2
  type-Module-CRing = type-Ab ab-Module-CRing

  add-Module-CRing : (x y : type-Module-CRing) → type-Module-CRing
  add-Module-CRing = add-Ab ab-Module-CRing

  mul-hom-Module-CRing :
    hom-Ring (ring-Commutative-Ring R)
    ( endomorphism-ring-ab-left-module-Ring (ring-Commutative-Ring R) M)
  mul-hom-Module-CRing = mul-hom-left-module-Ring (ring-Commutative-Ring R) M

  zero-Module-CRing : type-Module-CRing
  zero-Module-CRing = zero-Ab ab-Module-CRing

  is-zero-Module-CRing : type-Module-CRing → UU l2
  is-zero-Module-CRing = is-zero-Ab ab-Module-CRing

  neg-Module-CRing : type-Module-CRing → type-Module-CRing
  neg-Module-CRing = neg-Ab ab-Module-CRing
```

## Properties

### The categories of left and right `R`-modules are equivalent

This remains to be formalized.
