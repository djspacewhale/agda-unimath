# Lyndon words

```agda
module lists.lyndon-words where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.posets

open import lists.lexicographic-orders
open import lists.lists
open import lists.conjugacy-classes-lists
open import lists.prefixes-lists
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
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
- [Lyndon word](https://en.wikipedia.org/wiki/Lyndon_word) at Wikipedia
