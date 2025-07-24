# Dependent products of left modules over a ring

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.dependent-products-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids
open import group-theory.semigroups

open import linear-algebra.left-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

Given a family of (left `R`-)modules `Mᵢ` indexed by `i : I`, the dependent
product `Π(i : I), Mᵢ` is the left module consisting of dependent functions
assigning to each `i : I` an element of the underlying type of `Mᵢ`. The module
operations are given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : UU l2) (M : I → left-module-Ring l3 R)
  where

  ab-Π-left-module-Ring : Ab (l2 ⊔ l3)
  ab-Π-left-module-Ring = Π-Ab I (λ i → ab-left-module-Ring R (M i))

  ab-hom-Π-left-module-Ring :
    hom-Ab (ab-Ring R) (ab-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring))
  pr1 (pr1 ab-hom-Π-left-module-Ring r) x i =
    mul-left-module-Ring R (M i) r (x i)
  pr2 (pr1 ab-hom-Π-left-module-Ring r) = eq-htpy
    ( λ x → pr2 (pr1 (pr1 (pr2 (M x))) r))
  pr2 ab-hom-Π-left-module-Ring {r} {s} =
    eq-htpy-hom-Ab ab-Π-left-module-Ring ab-Π-left-module-Ring htpy
    where
    htpy : htpy-hom-Ab (Π-Ab I (λ i → pr1 (M i))) (Π-Ab I (λ i → pr1 (M i)))
      ( pr1 ab-hom-Π-left-module-Ring
      ( pr1 (pr2 (pr1 (pr1 (ab-Ring R)))) r s))
      ( pr1 (pr2 (pr1 (pr1
      ( ab-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring)))))
      ( pr1 ab-hom-Π-left-module-Ring r)
      ( pr1 ab-hom-Π-left-module-Ring s))
    htpy x = eq-htpy htpy2
      where
      htpy2 : pr1 (pr1 ab-hom-Π-left-module-Ring
        ( pr1 (pr2 (pr1 (pr1 (ab-Ring R)))) r s)) x
        ~ pr1 (pr1 (pr2
        ( pr1 (pr1 (ab-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring)))))
        ( pr1 ab-hom-Π-left-module-Ring r) (pr1 ab-hom-Π-left-module-Ring s)) x
      htpy2 i =
        {!   !}
        ∙ ( right-distributive-mul-add-left-module-Ring R (M i) r s (x i))
        ∙ {!   !}

  ab-hom-is-ring-hom-Π-left-module-Ring :
    is-ring-homomorphism-hom-Ab R (endomorphism-ring-Ab ab-Π-left-module-Ring)
    ab-hom-Π-left-module-Ring
  pr1 ab-hom-is-ring-hom-Π-left-module-Ring {r} {s} =
    eq-htpy-hom-Ab ab-Π-left-module-Ring ab-Π-left-module-Ring htpy
    where
    htpy : htpy-hom-Ab (Π-Ab I (λ i → pr1 (M i))) (Π-Ab I (λ i → pr1 (M i)))
      ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
      ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
      ab-hom-Π-left-module-Ring))
      ( pr1 (pr2 (multiplicative-semigroup-Semiring (semiring-Ring R))) r s))
      ( pr1 (pr2 (multiplicative-semigroup-Semiring
      ( semiring-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring))))
      ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
      ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
      ab-hom-Π-left-module-Ring)) r)
      ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
      ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
      ab-hom-Π-left-module-Ring)) s))
    htpy x = eq-htpy htpy2
      where
      htpy2 : pr1 (pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
        ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
        ab-hom-Π-left-module-Ring)) (pr1 (pr2
        ( multiplicative-semigroup-Semiring (semiring-Ring R))) r s)) x
        ~ pr1 (pr1 (pr2 (multiplicative-semigroup-Semiring
        ( semiring-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring))))
        ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
        ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
        ab-hom-Π-left-module-Ring)) r)
        ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
        ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
        ab-hom-Π-left-module-Ring)) s)) x
      htpy2 i =
        {!   !}
        ∙ ( associative-mul-left-module-Ring R (M i) r s (x i))
        ∙ {!   !}
  pr2 ab-hom-is-ring-hom-Π-left-module-Ring =
    eq-htpy-hom-Ab ab-Π-left-module-Ring ab-Π-left-module-Ring htpy
    where
    htpy : htpy-hom-Ab (Π-Ab I (λ i → pr1 (M i))) (Π-Ab I (λ i → pr1 (M i)))
      ( pr1 (pr1
      ( hom-commutative-monoid-hom-Ab (pr1 R)
      ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
      ab-hom-Π-left-module-Ring))
      ( pr1 (pr2 (multiplicative-monoid-Semiring (semiring-Ring R)))))
      ( pr1 (pr2 (multiplicative-monoid-Semiring
      ( semiring-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring)))))
    htpy x = eq-htpy htpy2
      where
      htpy2 : pr1
        ( pr1 (pr1 (hom-commutative-monoid-hom-Ab (pr1 R)
        ( pr1 (endomorphism-ring-Ab ab-Π-left-module-Ring))
        ab-hom-Π-left-module-Ring))
        ( pr1 (pr2 (multiplicative-monoid-Semiring (semiring-Ring R))))) x
        ~ pr1 (pr1 (pr2 (multiplicative-monoid-Semiring
        ( semiring-Ring (endomorphism-ring-Ab ab-Π-left-module-Ring))))) x
      htpy2 i =
        {!   !}
        ∙ (left-unit-law-mul-left-module-Ring R (M i) (x i))

  action-Π-left-module-Ring :
    hom-Ring R (endomorphism-ring-Ab ab-Π-left-module-Ring)
  pr1 action-Π-left-module-Ring = ab-hom-Π-left-module-Ring
  pr2 action-Π-left-module-Ring = ab-hom-is-ring-hom-Π-left-module-Ring

  Π-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  pr1 Π-left-module-Ring = ab-Π-left-module-Ring
  pr2 Π-left-module-Ring = action-Π-left-module-Ring
```
