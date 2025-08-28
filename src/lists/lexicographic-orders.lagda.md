# The lexicographic order on lists in an ordered set

```agda
module lists.lexicographic-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.unit-type
open import foundation.empty-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import lists.concatenation-lists
open import lists.lists
open import lists.prefixes-lists

open import order-theory.posets
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

  lex-order-list : Relation-Prop (l1 ⊔ l2) (list (type-Poset A))
  lex-order-list nil v = raise-unit-Prop (l1 ⊔ l2)
  lex-order-list (cons x m) nil = raise-empty-Prop (l1 ⊔ l2)
  lex-order-list (cons x u) (cons y v) =
    is-set-is-prefix-list-Prop (cons x u) (is-set-type-Poset A) (cons y v) ∨
    ( ∃ (list (type-Poset A)) (λ u →
      ( ∃ (list (type-Poset A)) (λ v →
        ( ∃ (list (type-Poset A)) (λ w →
          ( ∃ (type-Poset A) (λ a →
            ( ∃ (type-Poset A) (λ b → le-prop-Poset A a b ∧
              Id-Prop (list-Set (set-Poset A)) (cons x u) (concat-list u (cons x v)) ∧
              Id-Prop (list-Set (set-Poset A)) (cons y v) (concat-list u (cons y w))))))))))))
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
- [Lexicographic order](https://en.wikipedia.org/wiki/Lexicographic_order) at
  Wikipedia
