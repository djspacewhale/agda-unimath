# Finite posets

```agda
module order-theory.finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections

open import order-theory.finite-preorders
open import order-theory.posets
open import order-theory.preorders

open import univalent-combinatorics.finite-types
```

</details>

## Definitions

A **finite poset** is a [poset](order-theory.posets.md) of which the underlying
type is [finite](univalent-combinatorics.finite-types.md), and of which the
ordering relation is [decidable](foundation.decidable-relations.md).

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-finite-Poset-Prop : Prop (l1 ⊔ l2)
  is-finite-Poset-Prop = is-finite-Preorder-Prop (preorder-Poset P)

  is-finite-Poset : UU (l1 ⊔ l2)
  is-finite-Poset = is-finite-Preorder (preorder-Poset P)

  is-prop-is-finite-Poset : is-prop is-finite-Poset
  is-prop-is-finite-Poset = is-prop-is-finite-Preorder (preorder-Poset P)

  is-finite-type-is-finite-Poset :
    is-finite-Poset → is-finite (type-Poset P)
  is-finite-type-is-finite-Poset =
    is-finite-type-is-finite-Preorder (preorder-Poset P)

  is-decidable-leq-is-finite-Poset :
    is-finite-Poset → (x y : type-Poset P) → is-decidable (leq-Poset P x y)
  is-decidable-leq-is-finite-Poset =
    is-decidable-leq-is-finite-Preorder (preorder-Poset P)

Finite-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Poset l1 l2 =
  Σ ( Finite-Preorder l1 l2)
    ( λ P → is-antisymmetric-leq-Preorder (preorder-Finite-Preorder P))

finite-preorder-Finite-Poset :
  {l1 l2 : Level} → Finite-Poset l1 l2 → Finite-Preorder l1 l2
finite-preorder-Finite-Poset = pr1

preorder-Finite-Poset : {l1 l2 : Level} → Finite-Poset l1 l2 → Preorder l1 l2
preorder-Finite-Poset = preorder-Finite-Preorder ∘ pr1

is-antisymmetric-leq-Finite-Poset :
  {l1 l2 : Level} (P : Finite-Poset l1 l2) →
  is-antisymmetric-leq-Preorder (preorder-Finite-Poset P)
is-antisymmetric-leq-Finite-Poset = pr2

poset-Finite-Poset : {l1 l2 : Level} → Finite-Poset l1 l2 → Poset l1 l2
pr1 (poset-Finite-Poset P) = preorder-Finite-Poset P
pr2 (poset-Finite-Poset P) = is-antisymmetric-leq-Finite-Poset P
```

## Properties

### Finite posets are exactly the posets which are finite

```agda
Finite-Poset' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Poset' l1 l2 = Σ (Poset l1 l2) (λ P → is-finite-Poset P)

Finite-Poset-to-Finite-Poset' :
  ( l1 l2 : Level) → Finite-Poset l1 l2 → Finite-Poset' l1 l2
pr1 (pr1 (pr1 (Finite-Poset-to-Finite-Poset' l1 l2 ((P , _) , _)))) = pr1 P
pr1 (pr2 (pr1 (pr1 (Finite-Poset-to-Finite-Poset' l1 l2 ((P , <) , _))))) x y =
  pair (pr1 (pr1 < x y)) (pr1 (pr2 (pr1 < x y)))
pr2 (pr2 (pr1 (pr1 (Finite-Poset-to-Finite-Poset' l1 l2 ((P , <) , _))))) =
  pr2 <
pr2 (pr1 (Finite-Poset-to-Finite-Poset' l1 l2 (P , P-antisym))) = P-antisym
pr2 (Finite-Poset-to-Finite-Poset' l1 l2 (P , _)) =
  pair (pr2 (pr1 P)) (λ x y → pr2 (pr2 (pr1 (pr2 P) x y)))

Finite-Poset'-to-Finite-Poset :
  ( l1 l2 : Level) → Finite-Poset' l1 l2 → Finite-Poset l1 l2
pr1 (pr1 (Finite-Poset'-to-Finite-Poset l1 l2 (P , P-fin))) =
  pair (pr1 (pr1 P)) (pr1 P-fin)
pr1 (pr2 (pr1 (Finite-Poset'-to-Finite-Poset l1 l2 (P , P-fin)))) = λ x y →
  pair (pr1 (pr1 (pr2 (pr1 P)) x y))
  ( pair (pr2 (pr1 (pr2 (pr1 P)) x y)) (pr2 P-fin x y))
pr2 (pr2 (pr1 (Finite-Poset'-to-Finite-Poset l1 l2 (P , P-fin)))) =
  pr2 (pr2 (pr1 P))
pr2 (Finite-Poset'-to-Finite-Poset l1 l2 (P , P-fin)) = pr2 P

is-equiv-Finite-Poset-to-Finite-Poset' :
  ( l1 l2 : Level) → is-equiv (Finite-Poset-to-Finite-Poset' l1 l2)
pr1 (pr1 (is-equiv-Finite-Poset-to-Finite-Poset' l1 l2)) =
  Finite-Poset'-to-Finite-Poset l1 l2
pr2 (pr1 (is-equiv-Finite-Poset-to-Finite-Poset' l1 l2)) P = refl
pr1 (pr2 (is-equiv-Finite-Poset-to-Finite-Poset' l1 l2)) =
  Finite-Poset'-to-Finite-Poset l1 l2
pr2 (pr2 (is-equiv-Finite-Poset-to-Finite-Poset' l1 l2)) P = refl
```
