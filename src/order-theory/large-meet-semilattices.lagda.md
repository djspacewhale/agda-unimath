# Large meet-semilattices

```agda
module order-theory.large-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-posets
```

</details>

## Idea

A **large meet-semilattice** is a
[large semigroup](group-theory.large-semigroups.md) which is commutative and
idempotent.

## Definition

### The predicate that an element of a large poset is a lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UU (β l3 l1 ⊔ β l3 l2)
  is-binary-lower-bound-Large-Poset x =
    leq-Large-Poset P x a × leq-Large-Poset P x b
```

### The predicate that an element of a large poset is the greatest lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-greatest-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UUω
  is-greatest-binary-lower-bound-Large-Poset x =
    {l4 : Level} (y : type-Large-Poset P l4) →
    is-binary-lower-bound-Large-Poset P a b y ↔ leq-Large-Poset P y x
```

### The predicate that a large poset has meets

```agda
record
  has-meets-Large-Poset
    { α : Level → Level}
    { β : Level → Level → Level}
    ( P : Large-Poset α β) :
    UUω
  where
  constructor
    make-has-meets-Large-Poset
  field
    meet-has-meets-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      type-Large-Poset P (l1 ⊔ l2)
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      is-greatest-binary-lower-bound-Large-Poset P x y
        ( meet-has-meets-Large-Poset x y)

open has-meets-Large-Poset public
```

### Large meet-semilattices

```agda
record
  Large-Meet-Semilattice
    ( α : Level → Level)
    ( β : Level → Level → Level) :
    UUω
  where
  constructor
    make-Large-Meet-Semilattice
  field
    large-poset-Large-Meet-Semilattice :
      Large-Poset α β
    has-meets-Large-Meet-Semilattice :
      has-meets-Large-Poset large-poset-Large-Meet-Semilattice

open Large-Meet-Semilattice public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Meet-Semilattice α β)
  where

  type-Large-Meet-Semilattice : (l : Level) → UU (α l)
  type-Large-Meet-Semilattice =
    type-Large-Poset (large-poset-Large-Meet-Semilattice L)

  set-Large-Meet-Semilattice : (l : Level) → Set (α l)
  set-Large-Meet-Semilattice =
    set-Large-Poset (large-poset-Large-Meet-Semilattice L)

  is-set-type-Large-Meet-Semilattice :
    {l : Level} → is-set (type-Large-Meet-Semilattice l)
  is-set-type-Large-Meet-Semilattice =
    is-set-type-Large-Poset (large-poset-Large-Meet-Semilattice L)

  leq-Large-Meet-Semilattice :
    {l1 l2 : Level} →
    type-Large-Meet-Semilattice l1 → type-Large-Meet-Semilattice l2 →
    UU (β l1 l2)
  leq-Large-Meet-Semilattice =
    leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  refl-leq-Large-Meet-Semilattice :
    {l1 : Level} →
    (x : type-Large-Meet-Semilattice l1) → leq-Large-Meet-Semilattice x x
  refl-leq-Large-Meet-Semilattice =
    refl-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  antisymmetric-leq-Large-Meet-Semilattice :
    {l1 : Level} →
    (x y : type-Large-Meet-Semilattice l1) →
    leq-Large-Meet-Semilattice x y → leq-Large-Meet-Semilattice y x → x ＝ y
  antisymmetric-leq-Large-Meet-Semilattice =
    antisymmetric-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  transitive-leq-Large-Meet-Semilattice :
    {l1 l2 l3 : Level}
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2)
    (z : type-Large-Meet-Semilattice l3) →
    leq-Large-Meet-Semilattice y z → leq-Large-Meet-Semilattice x y →
    leq-Large-Meet-Semilattice x z
  transitive-leq-Large-Meet-Semilattice =
    transitive-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  meet-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2) →
    type-Large-Meet-Semilattice (l1 ⊔ l2)
  meet-Large-Meet-Semilattice =
    meet-has-meets-Large-Poset (has-meets-Large-Meet-Semilattice L)

  is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( x)
      ( y)
      ( meet-Large-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
      ( has-meets-Large-Meet-Semilattice L)
```