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

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.images-of-abelian-group-homomorphisms
open import group-theory.kernels-homomorphisms-abelian-groups

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
  `d n : C n → C (n - 1)` such that `image-hom-Ab d n ⊆ kernel-hom-Ab d (n - 1)`
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

  is-chain-structure-boundary-structure-Ab : boundary-structure-Ab → UU l
  is-chain-structure-boundary-structure-Ab D =
    ( n : ℤ) → (x : type-Ab (C (pred-ℤ n))) →
    is-in-im-hom-Ab (C n) (C (pred-ℤ n)) (D n) x →
    is-in-kernel-hom-Ab (C (pred-ℤ n)) (C (pred-ℤ (pred-ℤ n))) (D (pred-ℤ n)) x

  is-prop-is-chain-structure-boundary-structure-Ab :
    (D : boundary-structure-Ab) →
    is-prop (is-chain-structure-boundary-structure-Ab D)
  is-prop-is-chain-structure-boundary-structure-Ab D =
    is-prop-Π (λ n → is-prop-Π (λ x → is-prop-Π
    ( λ _ → pr2 (pr1 (pr1 (pr1 (C (pred-ℤ (pred-ℤ n))))))
      (pr1 (pr1 (pr2 (pr1 (C (pred-ℤ (pred-ℤ n)))))))
      (pr1 (D (pred-ℤ n)) x))))

  is-chain-structure-boundary-structure-Ab-Prop :
    boundary-structure-Ab → Prop l
  is-chain-structure-boundary-structure-Ab-Prop D =
    is-chain-structure-boundary-structure-Ab D ,
    is-prop-is-chain-structure-boundary-structure-Ab D

Chain-Complex-Ab : (l : Level) → UU (lsuc l)
Chain-Complex-Ab l =
  Σ (graded-Ab l) (λ C → Σ (boundary-structure-Ab C)
    ( is-chain-structure-boundary-structure-Ab C))
```
