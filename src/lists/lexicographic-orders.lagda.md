# The lexicographic order on lists in an ordered set

```agda
module lists.lexicographic-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.existential-quantification
open import foundation-core.identity-types
open import lists.lists
open import lists.prefixes-lists
open import lists.concatenation-lists
open import order-theory.posets
open import foundation-core.propositions
open import foundation.conjunction
open import foundation.disjunction
open import foundation-core.sets
```

</details>

## Idea

Recall that a **dictionary** is a dependent pair of an ordered list of words
and, for each word `w ∈ list A` in the language, a definition of `w`. Of
interest at the moment is that ordering of words - the alphabet is ordered, say,
`a < b < ... < y < z`, and this induces an order on words in the dictionary -
`apple < apricot < banana < bonanza < ...`, reading off the letters in a row and
flagging when the `n`th letter of one word is less than the `n`th letter of the
other.

More formally: for an [ordered set](order-theory.posets.md) `(A , <)`, the
{{#concept "lexicographic order" Disambiguation="on `list A`" Agda=lex-order-list}}
is defined as follows. For words `a , b`, we say `a < b` when any of the
following hold:

- `a` is a [prefix](lists.prefixes-lists.md) of `b`
- There exist words `u v w` and elements `x y ∈ A` such that:
  - `x < y`
  - `a = uxv`
  - `b = uyw`

Additional properties on the ordering of `A` ensure nice properties on the
lexicographic ordering of `list A` - for example, if `(A , <)` is a total order,
then `(list A, <)` is also totally ordered.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Poset l1 l2)
  where

  lex-order-list : list (type-Poset A) → list (type-Poset A) → Prop (l1 ⊔ l2)
  lex-order-list m n =
    is-set-is-prefix-list-Prop m (is-set-type-Poset A) n ∨
    ( ∃ (list (type-Poset A)) (λ u →
      ( ∃ (list (type-Poset A)) (λ v →
        ( ∃ (list (type-Poset A)) (λ w →
          ( ∃ (type-Poset A) (λ x →
            ( ∃ (type-Poset A) (λ y → le-prop-Poset A x y ∧
              Id-Prop (list-Set (set-Poset A)) m (concat-list u (cons x v)) ∧
              Id-Prop (list-Set (set-Poset A)) n (concat-list u (cons y w))))))))))))
```
