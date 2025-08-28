# Prefixes in lists

```agda
module lists.prefixes-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.transport-along-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.sets

open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Let `A : UU` and `l : list A`. Perhaps `l` decomposes into two lists, in the
sense that there exist lists `m , n` and an identification
`p : concat-list m n = l`. In this case, `m` is called a
{{#concept "prefix" Disambiguation="of `l`" Agda=prefix-list}}. When `A` is a
set, being a prefix of a fixed `l` is a property of lists.

## Definition

```agda
module _
  {l1 : Level} {A : UU l1} (l : list A)
  where

  is-prefix-list : list A → UU l1
  is-prefix-list m = Σ (list A) (λ n → Eq-list l (concat-list m n))

  prefix-list : UU l1
  prefix-list = Σ (list A) is-prefix-list

  list-prefix-list : prefix-list → list A
  list-prefix-list = pr1

  abstract
    is-set-all-elements-equal-is-prefix-list :
      is-set A → (m : list A) → all-elements-equal (is-prefix-list m)
    is-set-all-elements-equal-is-prefix-list set-A m (n , mn＝l) (p , mp＝l) =
      eq-pair-Σ
        ( is-injective-left-concat-list
          ( m)
          ( inv
            ( eq-Eq-list l (concat-list m n) mn＝l) ∙
            ( eq-Eq-list l (concat-list m p) mp＝l)))
        ( eq-is-prop
          ( is-prop-equiv
            ( inv-equiv (equiv-Eq-list l (concat-list m p)))
            ( is-set-list set-A l (concat-list m p))))

  is-set-is-prop-is-prefix-list :
    is-set A → (m : list A) → is-prop (is-prefix-list m)
  is-set-is-prop-is-prefix-list set-A m =
    is-prop-all-elements-equal (is-set-all-elements-equal-is-prefix-list set-A m)

  is-set-is-prefix-list-Prop : is-set A → list A → Prop l1
  is-set-is-prefix-list-Prop set-A m =
    ( is-prefix-list m) , is-set-is-prop-is-prefix-list set-A m
```

## Properties

### Relative tails of prefixes of lists

A **relative tail** of a prefix `p` of a word `l` is a word `q` such that
`l = pq`.

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  relative-tail :
    (l : list A) (p : prefix-list l) → list A
  relative-tail l (p , q , _) = q
```

### Suffixes

The above conversation readily dualizes to talk about `n` as a
{{#concept "suffix" Disambiguation="of `l`" Agda=suffix-list}}.

```agda
module _
  {l1 : Level} {A : UU l1} (l : list A)
  where

  is-suffix-list : list A → UU l1
  is-suffix-list m = Σ (list A) (λ n → Eq-list l (concat-list n m))

  suffix-list : UU l1
  suffix-list = Σ (list A) is-suffix-list

  is-set-all-elements-equal-is-suffix-list :
    is-set A → (m : list A) → all-elements-equal (is-suffix-list m)
  is-set-all-elements-equal-is-suffix-list set-A m (n , nm＝l) (p , pm＝l) =
    eq-pair-Σ
    ( is-injective-right-concat-list
      ( m)
      ( inv (eq-Eq-list l (concat-list n m) nm＝l) ∙
        eq-Eq-list l (concat-list p m) pm＝l))
    ( eq-is-prop
      ( is-prop-equiv
        ( inv-equiv (equiv-Eq-list l (concat-list p m)))
        ( is-set-list set-A l (concat-list p m))))

  is-set-is-prop-is-suffix-list :
    is-set A → (m : list A) → is-prop (is-suffix-list m)
  is-set-is-prop-is-suffix-list set-A m =
    is-prop-all-elements-equal (is-set-all-elements-equal-is-suffix-list set-A m)

  is-set-is-suffix-list-Prop : is-set A → list A → Prop l1
  is-set-is-suffix-list-Prop set-A m =
    ( is-suffix-list m) , is-set-is-prop-is-suffix-list set-A m

  list-suffix-list : suffix-list → list A
  list-suffix-list = pr1
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
