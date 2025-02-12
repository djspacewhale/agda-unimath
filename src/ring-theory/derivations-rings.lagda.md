# Derivations of rings

```agda
module ring-theory.derivations-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.modules-rings
open import ring-theory.rings
```

</details>

## Idea

**Derivations** are, roughly speaking, infinitesimal deformations of
[rings](ring-theory.rings.md). Strictly, a
[non-unital ring map](ring-theory.homomorphisms-rings.md) `d : R → R` - that is,
a map of underlying [abelian groups](group-theory.abelian-groups.md) - is a
derivation when it satisfies Leibniz' law:
` d (a *R b) ＝ (a *R (d b)) +R ((d a) *R b)`.

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  abstract
    _+R_ : type-Ring R → type-Ring R → type-Ring R
    _+R_ = add-Ring R

    _*R_ : type-Ring R → type-Ring R → type-Ring R
    _*R_ = mul-Ring R

  is-derivation-prop : (d : hom-Ab (ab-Ring R) (ab-Ring R)) → Prop l
  is-derivation-prop d = ∀' (type-Ring R) (λ a → ∀' (type-Ring R) (λ b → Id-Prop (set-Ring R) (d' (a *R b)) ((a *R d' b) +R (d' a *R b)))) where
    d' : type-Ring R → type-Ring R
    d' = map-hom-Ab (ab-Ring R) (ab-Ring R) d

  is-derivation : (d : hom-Ab (ab-Ring R) (ab-Ring R)) → UU l
  is-derivation d = type-Prop (is-derivation-prop d)

  derivation-Ring : UU l
  derivation-Ring = Σ (hom-Ab (ab-Ring R) (ab-Ring R)) λ d → is-derivation d

  is-prop-is-derivation : (d : hom-Ab (ab-Ring R) (ab-Ring R)) → is-prop (is-derivation d)
  is-prop-is-derivation d = is-prop-type-Prop (is-derivation-prop d)
```

## Properties

### The derivations of `R` form an `R`-module

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-derivation-Ring : derivation-Ring R
  pr1 zero-derivation-Ring = zero-hom-Ab (pr1 R) (pr1 R)
  pr2 zero-derivation-Ring x y = equational-reasoning
    pr1 (pr1 zero-derivation-Ring) ((R *R x) y) ＝ zero-Ring R
      by refl
    ＝ add-Ring R (zero-Ring R) (zero-Ring R)
      by inv (left-unit-law-add-Ring R (zero-Ring R))
    ＝ {! add-Ring R  !}
      by {!   !}

  add-derivation-Ring : derivation-Ring R → derivation-Ring R → derivation-Ring R
  pr1 (add-derivation-Ring (d , d-der) (e , e-der)) = add-hom-Ab (pr1 R) (pr1 R) d e
  pr2 (add-derivation-Ring d e) x y = {!   !}
```

### The commutator of derivations is a derivation

```agda
module _
  {l : Level} (R : Ring l)
  where
```
