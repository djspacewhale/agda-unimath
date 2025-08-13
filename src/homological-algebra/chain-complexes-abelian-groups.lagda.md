# Chain complexes of abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module homological-algebra.chain-complexes-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.images-of-abelian-group-homomorphisms
open import group-theory.kernels-homomorphisms-abelian-groups
open import group-theory.subgroups-abelian-groups

open import homological-algebra.graded-abelian-groups
```

</details>

## Idea

A
{{concept "chain complex" Disambiguation="of abelian groups" Agda=Chain-Complex-Ab}}
is:

- a [graded abelian group](homological-algebra.graded-abelian-groups.md)
  `(n : ℤ) → C n`
- for each `n : ℤ`, a [map](group-theory.homomorphisms-abelian-groups.md)
  `d n : C n → C (n - 1)` such that `image-hom-Ab d (n + 1) ⊆ kernel-hom-Ab d n`
  for all `n : ℤ`.

As chain complexes are an infinitary structure, issues of predicativity arise.
What we define in this module may be considered "small chain complexes", while
polymorphic/impredicative chain complexes will be defined elsewhere.

## Definition

```agda
module _
  {l : Level} (C : graded-Ab l)
  where

  boundary-structure-Ab : UU l
  boundary-structure-Ab = (n : ℤ) → hom-Ab (C n) (C (pred-ℤ n))

  is-chain-structure-boundary-structure-Ab-Prop :
    boundary-structure-Ab → Prop l
  is-chain-structure-boundary-structure-Ab-Prop d =
    Π-Prop ℤ (λ n → leq-prop-Subgroup-Ab (C n)
    ( image-hom-Ab (C (succ-ℤ n)) (C n) (D n))
    ( kernel-hom-Ab (C n) (C (pred-ℤ n)) (d n)))
      where
      D : (n : ℤ) → hom-Ab (C (succ-ℤ n)) (C n)
      D n =
        tr
        ( λ x → hom-Ab (C (succ-ℤ n)) (C x))
        ( is-retraction-pred-ℤ n)
        ( d (succ-ℤ n))

  is-chain-structure-boundary-structure-Ab :
    boundary-structure-Ab → UU l
  is-chain-structure-boundary-structure-Ab d = type-Prop (is-chain-structure-boundary-structure-Ab-Prop d)

Chain-Complex-Ab : (l : Level) → UU (lsuc l)
Chain-Complex-Ab l =
  Σ ( graded-Ab l) (λ C → Σ (boundary-structure-Ab C)
    ( λ d → is-chain-structure-boundary-structure-Ab C d))
```
