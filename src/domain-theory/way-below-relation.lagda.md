# The way-below relation in a dcpo

```agda
module domain-theory.way-below-relation where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-complete-posets

open import order-theory.directed-families-posets

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Elements `x y : type-Directed-Complete-Poset P` can be "way below" one another.
Say this - that `x` is **way below** `y` - if for all
[directed sets](order-theory.directed-families-posets)
`D : directed-family-Poset _ (poset-Directed-Complete-Poset P)` with
[sup](order-theory.least-upper-bounds-posets.md)
`s = sup-Directed-Complete-Poset P D`, whenever `y < s`, there
[exists](foundation.existential-quantification) some
`d : type-directed-family-Poset D` with
`x < family-directed-family-Poset P D d`.

Note: although the way-below relation may be defined in any poset (relative to
some universe level indexing directed sets), the relation is predicatively
difficult to define, and most useful in the context of dcpo's. Thus, we define
it in this domain-theoretic setting following
[Tom de Jong's thesis](https://tdejong.com/writings/phd-thesis.pdf) (section
4.2).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Directed-Complete-Poset l1 l2 l3)
  where

  is-way-below-Directed-Complete-Poset : (x y : type-Directed-Complete-Poset P) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-way-below-Directed-Complete-Poset x y = (D : directed-family-Poset l3 (poset-Directed-Complete-Poset P)) → leq-Directed-Complete-Poset P y (sup-Directed-Complete-Poset P D) → exists (type-directed-family-Poset (poset-Directed-Complete-Poset P) D) λ d → leq-prop-Directed-Complete-Poset P x (family-directed-family-Poset (poset-Directed-Complete-Poset P) D d)

  is-way-below-exists-Directed-Complete-Poset : (x y : type-Directed-Complete-Poset P) → is-way-below-Directed-Complete-Poset x y → (D : directed-family-Poset l3 (poset-Directed-Complete-Poset P)) → leq-Directed-Complete-Poset P y (sup-Directed-Complete-Poset P D) → exists (type-directed-family-Poset (poset-Directed-Complete-Poset P) D) λ d → leq-prop-Directed-Complete-Poset P x (family-directed-family-Poset (poset-Directed-Complete-Poset P) D d)
  is-way-below-exists-Directed-Complete-Poset x y way D y<d = way D y<d

  is-compact-element-Directed-Complete-Poset : type-Directed-Complete-Poset P → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-compact-element-Directed-Complete-Poset x = is-way-below-Directed-Complete-Poset x x
```

## Properties

### Way-belowness implies less-than

```agda
module _
  {l1 l2 l3 : Level} (P : Directed-Complete-Poset l1 l2 l3) (x y : type-Directed-Complete-Poset P)
  where

  is-way-below-is-leq : is-way-below-Directed-Complete-Poset P x y → leq-Directed-Complete-Poset P x y
  is-way-below-is-leq way = {!   !}
```
