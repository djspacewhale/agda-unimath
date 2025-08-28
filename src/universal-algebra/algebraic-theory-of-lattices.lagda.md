# The algebraic theory of lattices

```agda
module universal-algebra.algebraic-theory-of-lattices where
```

<details><summary><Imports></summary>

```agda
open import elementary-number-theory.natural-numbers
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation-core.identity-types
open import lists.tuples
open import order-theory.lattices
open import foundation-core.propositions
open import universal-algebra.algebraic-theories
open import universal-algebra.signatures
open import foundation.binary-relations
open import order-theory.lower-bounds-posets
open import order-theory.upper-bounds-posets
open import foundation.logical-equivalences
open import foundation.action-on-identifications-functions
open import foundation-core.sets
open import foundation-core.equivalences
open import universal-algebra.terms-over-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.algebras-of-theories
```

</details>

## Idea

[Lattices](order-theory.lattices.md) are a nice example of a class of seemingly
non-algebraic objects that fall under the purview of universal algebra. In this
setting, a {{#concept "lattice" Agda=lattice-Algebra}} is a
[model](universal-algebra.models-of-signatures.md) of the
[signature](universal-algebra.signatures.md) with two binary operations `\_∧\_,
\_∨\_, [satisfying](universal-algebra.algebras-of-theories.md) the
[axioms](universal-algebra.algebraic-theories.md):

```text
- x ∨ y = y ∨ x
- x ∧ y = y ∧ x
- x ∨ (y ∨ z) = (x ∨ y) ∨ z
- x ∧ (y ∧ z) = (x ∧ y) ∧ z
- x ∨ x = x
- x ∧ x = x
- x = x ∨ (x ∧ y)
- x = x ∧ (x ∨ y)
```

```agda
data lattice-ops : UU lzero where
  join-lattice meet-lattice : lattice-ops

lattice-signature : signature lzero
pr1 lattice-signature = lattice-ops
pr2 lattice-signature join-lattice = 2
pr2 lattice-signature meet-lattice = 2

data lattice-laws : UU lzero where
  comm-join comm-meet : lattice-laws
  assoc-join assoc-meet : lattice-laws
  idem-join idem-meet : lattice-laws
  absorb-join absorb-meet : lattice-laws

lattice-Theory : Theory lattice-signature lzero
pr1 lattice-Theory = lattice-laws
pr2 lattice-Theory comm-join =
  ( ( op-Term join-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple)) ,
    ( op-Term join-lattice (var-Term 1 ∷ var-Term 0 ∷ empty-tuple)))
pr2 lattice-Theory comm-meet =
  ( ( op-Term meet-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple)) ,
    ( op-Term meet-lattice (var-Term 1 ∷ var-Term 0 ∷ empty-tuple)))
pr2 lattice-Theory assoc-join =
  ( ( op-Term join-lattice
      ( var-Term 0 ∷
        op-Term join-lattice (var-Term 1 ∷ var-Term 2 ∷ empty-tuple) ∷
        empty-tuple)) ,
    ( op-Term join-lattice
      (( op-Term join-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple)) ∷
        var-Term 2 ∷
        empty-tuple)))
pr2 lattice-Theory assoc-meet =
  ( ( op-Term meet-lattice
      ( var-Term 0 ∷
        op-Term meet-lattice (var-Term 1 ∷ var-Term 2 ∷ empty-tuple) ∷
        empty-tuple)) ,
    ( op-Term meet-lattice
      (( op-Term meet-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple)) ∷
      var-Term 2 ∷
      empty-tuple)))
pr2 lattice-Theory idem-join =
  ( var-Term 0 , op-Term join-lattice (var-Term 0 ∷ var-Term 0 ∷ empty-tuple))
pr2 lattice-Theory idem-meet =
  ( var-Term 0 , op-Term meet-lattice (var-Term 0 ∷ var-Term 0 ∷ empty-tuple))
pr2 lattice-Theory absorb-join =
  ( var-Term 0 ,
    ( op-Term join-lattice
      ( var-Term 0 ∷
        op-Term meet-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple) ∷
        empty-tuple)))
pr2 lattice-Theory absorb-meet =
  ( var-Term 0 ,
    ( op-Term meet-lattice
      ( var-Term 0 ∷
        op-Term join-lattice (var-Term 0 ∷ var-Term 1 ∷ empty-tuple) ∷
        empty-tuple)))

lattice-Algebra : (l : Level) → UU (lsuc l)
lattice-Algebra l = Algebra lattice-signature lattice-Theory l

type-lattice-Algebra : {l : Level} → lattice-Algebra l → UU l
type-lattice-Algebra L = type-Algebra lattice-signature lattice-Theory L

set-lattice-Algebra : {l : Level} → lattice-Algebra l → Set l
set-lattice-Algebra L = set-Algebra lattice-signature lattice-Theory L

model-lattice-Algebra :
  {l : Level} → lattice-Algebra l → Model-Signature lattice-signature l
model-lattice-Algebra L = model-Algebra lattice-signature lattice-Theory L

structure-lattice-Algebra :
  {l : Level} (L : lattice-Algebra l) →
  is-model-signature lattice-signature (set-lattice-Algebra L)
structure-lattice-Algebra L =
  is-model-set-Algebra lattice-signature lattice-Theory L
```

## Properties

### Universal-algebraic lattices are order-theoretic lattices

Take `x ≤ y = (x ＝ (x ∧ y))`; the RHS is a proposition, as models are sets.
This order is reflexive by idempotence of the meet operation (`x ＝ x ∧ x`), and
transitive and antisymmetric by some equational reasoning.

```agda
leq-prop-lattice-Algebra-Lattice :
  {l : Level} (L : lattice-Algebra l) → Relation-Prop l (type-lattice-Algebra L)
leq-prop-lattice-Algebra-Lattice ((L , L-str) , _) x y =
  Id-Prop L x (L-str meet-lattice (x ∷ y ∷ empty-tuple))

leq-lattice-Algebra-Lattice :
  {l : Level} (L : lattice-Algebra l) → (x y : type-lattice-Algebra L) → UU l
leq-lattice-Algebra-Lattice L x y =
  type-Prop (leq-prop-lattice-Algebra-Lattice L x y)

is-reflexive-lattice-Algebra-Lattice :
  {l : Level} (L : lattice-Algebra l) →
  (x : type-lattice-Algebra L) →
  leq-lattice-Algebra-Lattice L x x
is-reflexive-lattice-Algebra-Lattice (L , L-alg) x = L-alg idem-meet (λ _ → x)

is-transitive-lattice-Algebra-Lattice :
  {l : Level} (L : lattice-Algebra l) →
  (x y z : type-lattice-Algebra L) →
  leq-lattice-Algebra-Lattice L y z →
  leq-lattice-Algebra-Lattice L x y →
  leq-lattice-Algebra-Lattice L x z
is-transitive-lattice-Algebra-Lattice ((L , L-str) , L-alg) x y z p q =
  equational-reasoning
    x
    ＝ L-str meet-lattice (x ∷ y ∷ empty-tuple)
      by q
    ＝ L-str meet-lattice
      ( x ∷ L-str meet-lattice (y ∷ z ∷ empty-tuple) ∷ empty-tuple)
      by ap (λ w → L-str meet-lattice (x ∷ w ∷ empty-tuple)) p
    ＝ L-str meet-lattice
      (( L-str meet-lattice (x ∷ y ∷ empty-tuple)) ∷ z ∷ empty-tuple)
      by L-alg assoc-meet
        ( λ where
            0 → x
            1 → y
            (succ-ℕ (succ-ℕ n)) → z)
    ＝ L-str meet-lattice (x ∷ z ∷ empty-tuple)
      by ap (λ w → L-str meet-lattice (w ∷ z ∷ empty-tuple)) (inv q)

is-antisymmetric-lattice-Algebra-Lattice :
  {l : Level} (L : lattice-Algebra l) →
  (x y : type-lattice-Algebra L) →
  (x ＝ structure-lattice-Algebra L meet-lattice (x ∷ y ∷ empty-tuple)) →
  (y ＝ structure-lattice-Algebra L meet-lattice (y ∷ x ∷ empty-tuple)) →
  x ＝ y
is-antisymmetric-lattice-Algebra-Lattice ((L , L-str) , L-alg) x y p q =
  equational-reasoning
  x
  ＝ L-str meet-lattice (x ∷ y ∷ empty-tuple)
    by p
  ＝ L-str meet-lattice (y ∷ x ∷ empty-tuple)
    by L-alg comm-meet
      ( λ where
          0 → x
          (succ-ℕ n) → y)
  ＝ y
    by inv q

lattice-Algebra-Lattice : {l : Level} → lattice-Algebra l → Lattice l l
pr1 (pr1 (pr1 (lattice-Algebra-Lattice (((L , _) , _) , _)))) = L
pr1 (pr2 (pr1 (pr1 (lattice-Algebra-Lattice L)))) =
  leq-prop-lattice-Algebra-Lattice L
pr1 (pr2 (pr2 (pr1 (pr1 (lattice-Algebra-Lattice L))))) =
  is-reflexive-lattice-Algebra-Lattice L
pr2 (pr2 (pr2 (pr1 (pr1 (lattice-Algebra-Lattice L))))) =
  is-transitive-lattice-Algebra-Lattice L
pr2 (pr1 (lattice-Algebra-Lattice L)) =
  is-antisymmetric-lattice-Algebra-Lattice L
pr1 (pr1 (pr2 (lattice-Algebra-Lattice ((L , L-str) , _))) x y) =
  L-str meet-lattice (x ∷ y ∷ empty-tuple)
pr2 (pr1 (pr2 (lattice-Algebra-Lattice L)) x y) z = {!   !}
pr1 (pr2 (pr2 (lattice-Algebra-Lattice ((L , L-str) , _))) x y) =
  L-str join-lattice (x ∷ y ∷ empty-tuple)
pr2 (pr2 (pr2 (lattice-Algebra-Lattice L)) x y) z = {!   !}
```

### Order-theoretic lattices are universal-algebraic lattices

In a sense, this is perhaps the more interesting direction, as universe levels
begin to take an important role in the formalization. In particular, the
universal-algebraic lattice of an order-theoretic lattice is _small_, in the
sense that an `L ∈ Lattice l1 l2` becomes an `L' ∈ lattice-Algebra l1`!

```agda
Lattice-lattice-Algebra : {l1 l2 : Level} → Lattice l1 l2 → lattice-Algebra l1
pr1 (pr1 (Lattice-lattice-Algebra L)) = set-Lattice L
pr2 (pr1 (Lattice-lattice-Algebra L)) join-lattice (x ∷ y ∷ empty-tuple) =
  join-Lattice L x y
pr2 (pr1 (Lattice-lattice-Algebra L)) meet-lattice (x ∷ y ∷ empty-tuple) =
  meet-Lattice L x y
pr2 (Lattice-lattice-Algebra L) = {!   !}
```

### The equivalence between order-theoretic lattices and universal-algebraic lattices

```agda
is-equiv-lattice-Algebra-Lattice :
  {l : Level} → is-equiv (lattice-Algebra-Lattice {l})
pr1 (pr1 is-equiv-lattice-Algebra-Lattice) = Lattice-lattice-Algebra
pr2 (pr1 is-equiv-lattice-Algebra-Lattice) = {!   !}
pr1 (pr2 is-equiv-lattice-Algebra-Lattice) = Lattice-lattice-Algebra
pr2 (pr2 is-equiv-lattice-Algebra-Lattice) = {!   !}

equiv-lattice-Algebra-Lattice : (l : Level) → lattice-Algebra l ≃ Lattice l l
pr1 (equiv-lattice-Algebra-Lattice l) = lattice-Algebra-Lattice
pr2 (equiv-lattice-Algebra-Lattice l) = is-equiv-lattice-Algebra-Lattice
```

Note that this equivalence only holds for "homogeneous" lattices, i.e. those `L`
with carrier type in `UU l` and `x ≤ y ∈ Prop l` the same universe level. What
of inhomogeneous lattices, which do appear in nature?

**Conjecture**: The following are
[equivalent](foundation.logical-equivalences.md):

- [Propositional resizing](foundation.propositional-resizing.md)
- "Lattice resizing": for any universe levels `l1, l2`, there is an equivalence
  `f : Lattice l1 l2 ≃ Lattice l1 l1` commuting with
  `lattice-Algebra-Lattice ∘ Lattice-lattice-Algebra`:

```text
    Lattice-lattice-Algebra l1 l2

Lattice l1 l2 -------> lattice-Algebra l1
      \                   /
       \                 /
      f \               / lattice-Algebra-Lattice l1
         \             /
          ∨           ∨
          Lattice l1 l1
```

Proof:

(->): The proposition `x ≤ y ∈ Prop l2` resizes to an equivalent proposition in
`Prop l1`, and the equivalence follows from general identity type
considerations.

(<-): We do one better and resize propositions down to `lzero`; they may then be
[raised](foundation.raising-universe-levels.md) as needed. Raise
[`bool`](foundation.booleans.md) to `UU l1` and consider it as a poset
`bool-Poset ∈ Poset l1 lzero` by
`false ≤ x = unit, x ≤ true = unit, true ≤ false = empty` (`bool` is of course
[locally small](foundation.locally-small-types.md), as its equality is
decidable). This is a lattice by rote computation.

Then, consider its [quotient](foundation.set-quotients.md) `bool / P` where
`(x ＝P y) = ((x ＝ y) ∨ P)`; this quotient is naturally a poset living in
`Poset (l1 ⊔ l2) l2`, and is again a lattice.

```agda
module lattice-resizing-propositional-resizing where

  open import foundation.propositional-resizing

  prop-resizing-equiv-lattice-Algebra :
    (l1 l2 : Level) → propositional-resizing → Lattice l1 l2 ≃ Lattice l1 l1
  pr1 (pr1 (pr1 (pr1 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) L))) =
    type-Lattice L
  pr1 (pr2 (pr1 (pr1 (pr1 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) L)))) x y =
    pr2 (pr1 (resize l1 l2)) (pr1 (pr2 (resize l1 l2) (leq-lattice-Prop L x y)))
  pr2 (pr2 (pr1 (pr1 (pr1 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) L)))) =
    {!   !}
  pr2 (pr1 (pr1 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) L)) = {!   !}
  pr2 (pr1 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) L) = {!   !}
  pr2 (prop-resizing-equiv-lattice-Algebra l1 l2 resize) = {!   !}
```
