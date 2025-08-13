# Lyndon words

```agda
module lists.lyndon-words where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation.dependent-pair-types
open import foundation-core.propositions

open import lists.lexicographic-orders
open import lists.lists
open import lists.prefixes-lists

open import order-theory.posets
```

</details>

## Idea

Consider an ordered set - say, `(Fin n , <)` - and a nonnil word
`w ∈ list (Fin n)`. There are several equivalent definitions for when `w` is a
{{#concept "Lyndon word" Agda=is-lyndon-word}}:

- For every [prefix](lists.prefixes-lists.md) `p` of `w`, `p` is
  [lexicographically](lists.lexicographic-orders.md) less than its relative tail
- `w` is the [unique](foundation-core.contractible-types.md) minimal element of
  its conjugacy class
- For every nonnil suffix `s` of `w`, we have that `w` is strictly smaller than
  `s`

## Definition

```agda
module _
  {l1 l2 : Level} (A : Poset l1 l2)
  where

  prefix-is-lex-less-than-tail-list : (l : list (type-Poset A)) → Prop (l1 ⊔ l2)
  prefix-is-lex-less-than-tail-list l =
    Π-Prop
    ( prefix-list l)
    ( λ p → lex-order-list A (pr1 p) (relative-tail l p))

  is-lex-less-than-suffix-list : (l : list (type-Poset A)) → Prop (l1 ⊔ l2)
  is-lex-less-than-suffix-list l =
    Π-Prop
    ( Σ (suffix-list l) (λ s → is-nonnil-list (pr1 s)))
    ( λ s → lex-order-list A l (pr1 (pr1 s)))
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
- [Lyndon word](https://en.wikipedia.org/wiki/Lyndon_word) at Wikipedia
