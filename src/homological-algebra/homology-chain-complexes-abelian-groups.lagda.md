# The homology of a chain complex of abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module homological-algebra.homology-chain-complexes-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation.action-on-identifications-functions
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
open import foundation-core.propositions

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.images-of-abelian-group-homomorphisms
open import group-theory.kernels-homomorphisms-abelian-groups
open import group-theory.quotients-abelian-groups
open import group-theory.subgroups-abelian-groups

open import homological-algebra.graded-abelian-groups
open import homological-algebra.chain-complexes-abelian-groups
```

</details>

## Idea

The property that the image of a boundary map in a
[chain complex](homological-algebra.chain-complexes-abelian-groups.md) is
contained in the kernel of the next boundary map suggests taking quotients of
the kernels modulo images. These
[quotient abelian groups](group-theory.quotients-abelian-groups.md) are the
{{concept "homology" Disambiguation="abelian groups" Agda=homology-chain-complex-Ab}}
of our complex.

## Definition

```agda
module _
  {l : Level} (n : ℤ)
  where

  homology-Chain-Complex-Ab : (C : Chain-Complex-Ab l) → Ab l
  homology-Chain-Complex-Ab (C , d , is-chain) =
    quotient-Ab
    ( ab-kernel-hom-Ab (C n) (C (pred-ℤ n)) (d n))
    (( λ (i , p) → subset-image-hom-Ab (C (succ-ℤ n)) (C n) Dn i) ,
      {!   !})
      where
      Dn : hom-Ab (C (succ-ℤ n)) (C n)
      Dn =
        tr
        ( λ x → hom-Ab (C (succ-ℤ n)) (C x))
        ( is-retraction-pred-ℤ n)
        ( d (succ-ℤ n))
```
