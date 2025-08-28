# Lyndon words

```agda
module lists.lyndon-words where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.disjunction
open import foundation-core.identity-types
open import foundation.unit-type
open import lists.concatenation-lists
open import foundation.existential-quantification
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
{{#concept "Lyndon word" Agda=Lyndon-Word}}:

- For every [prefix](lists.prefixes-lists.md) `p` of `w`, `p` is
  [lexicographically](lists.lexicographic-orders.md) less than its relative tail
- For every nonnil suffix `s` of `w`, we have that `w` is strictly smaller than
  `s`
- `w` is the [unique](foundation-core.contractible-types.md) minimal element of
  its conjugacy class

This last point of view depends on considering the multiset of conjugates of `w`
rather than the naive subtype, and remains to be formalized.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Poset l1 l2)
  where

  prefix-is-lex-less-than-tail-list-Prop : (l : list (type-Poset A)) → Prop (l1 ⊔ l2)
  prefix-is-lex-less-than-tail-list-Prop l =
    Π-Prop
    ( prefix-list l)
    ( λ p → lex-order-list A (list-prefix-list l p) (relative-tail l p))

  prefix-is-lex-less-than-tail-list : (l : list (type-Poset A)) → UU (l1 ⊔ l2)
  prefix-is-lex-less-than-tail-list l =
    type-Prop (prefix-is-lex-less-than-tail-list-Prop l)

  is-lex-less-than-suffix-list-Prop : (l : list (type-Poset A)) → Prop (l1 ⊔ l2)
  is-lex-less-than-suffix-list-Prop l =
    Π-Prop
    ( Σ (suffix-list l) (λ s → is-nonnil-list (list-suffix-list l s)))
    ( λ (s , _) → lex-order-list A l (list-suffix-list l s))

  is-lex-less-than-suffix-list : (l : list (type-Poset A)) → UU (l1 ⊔ l2)
  is-lex-less-than-suffix-list l =
    type-Prop (is-lex-less-than-suffix-list-Prop l)

  Lyndon-Word : UU (l1 ⊔ l2)
  Lyndon-Word =
    Σ (list (type-Poset A)) (λ l → is-lex-less-than-suffix-list l)
```

## Properties

### The three definitions are equivalent

For now, we show equivalence of the first two.

```agda
module _
  {l1 l2 : Level} (A : Poset l1 l2)
  where

  prefix-is-lex-less-than-tail-is-lex-less-than-suffix-list :
    (l : list (type-Poset A)) →
    is-lex-less-than-suffix-list A l → prefix-is-lex-less-than-tail-list A l
  prefix-is-lex-less-than-tail-is-lex-less-than-suffix-list nil p (nil , s , eq) =
    raise-star
  prefix-is-lex-less-than-tail-is-lex-less-than-suffix-list nil p (cons x pr , s , eq) =
    raise-ex-falso l1 eq
  prefix-is-lex-less-than-tail-is-lex-less-than-suffix-list (cons x l) p (pr , s , eq) = {!   !}

  is-lex-less-than-suffix-prefix-is-lex-less-than-tail-list :
    (l : list (type-Poset A)) →
    prefix-is-lex-less-than-tail-list A l → is-lex-less-than-suffix-list A l
  is-lex-less-than-suffix-prefix-is-lex-less-than-tail-list nil p ((s , pr , eq) , _) =
    raise-star
  is-lex-less-than-suffix-prefix-is-lex-less-than-tail-list (cons x l) p ((nil , nil , eq) , _) =
    raise-ex-falso l1 eq
  is-lex-less-than-suffix-prefix-is-lex-less-than-tail-list (cons x l) p ((nil , cons z pr , eq) , nn) =
    ex-falso (nn refl)
  is-lex-less-than-suffix-prefix-is-lex-less-than-tail-list (cons x l) p ((cons y s , pr , eq) , _) = {!   !}
```

## External links

- [Theory](https://www.lyndex.org/theory.php) at Lyndex Project
- [Lyndon word](https://en.wikipedia.org/wiki/Lyndon_word) at Wikipedia
