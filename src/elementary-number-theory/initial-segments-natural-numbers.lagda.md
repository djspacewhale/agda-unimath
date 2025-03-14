# Initial segments of the natural numbers

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module elementary-number-theory.initial-segments-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.retractions
open import foundation-core.sections

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An **initial segment** of the natural numbers is a subtype `P : ℕ → Prop` such
that the implication

```text
  P (n + 1) → P n
```

holds for every `n : ℕ`.

## Definitions

### Initial segments

```agda
is-initial-segment-subset-ℕ-Prop : {l : Level} (P : subtype l ℕ) → Prop l
is-initial-segment-subset-ℕ-Prop P =
  Π-Prop ℕ (λ n → hom-Prop (P (succ-ℕ n)) (P n))

is-initial-segment-subset-ℕ : {l : Level} (P : subtype l ℕ) → UU l
is-initial-segment-subset-ℕ P = type-Prop (is-initial-segment-subset-ℕ-Prop P)

initial-segment-ℕ : (l : Level) → UU (lsuc l)
initial-segment-ℕ l = type-subtype is-initial-segment-subset-ℕ-Prop

module _
  {l : Level} (I : initial-segment-ℕ l)
  where

  subset-initial-segment-ℕ : subtype l ℕ
  subset-initial-segment-ℕ = pr1 I

  is-initial-segment-initial-segment-ℕ :
    is-initial-segment-subset-ℕ subset-initial-segment-ℕ
  is-initial-segment-initial-segment-ℕ = pr2 I

  is-in-initial-segment-ℕ : ℕ → UU l
  is-in-initial-segment-ℕ = is-in-subtype subset-initial-segment-ℕ

  is-closed-under-eq-initial-segment-ℕ :
    {x y : ℕ} → is-in-initial-segment-ℕ x → x ＝ y → is-in-initial-segment-ℕ y
  is-closed-under-eq-initial-segment-ℕ =
    is-closed-under-eq-subtype subset-initial-segment-ℕ

  is-closed-under-eq-initial-segment-ℕ' :
    {x y : ℕ} → is-in-initial-segment-ℕ y → x ＝ y → is-in-initial-segment-ℕ x
  is-closed-under-eq-initial-segment-ℕ' =
    is-closed-under-eq-subtype' subset-initial-segment-ℕ
```

### Shifting initial segments

```agda
shift-initial-segment-ℕ :
  {l : Level} → initial-segment-ℕ l → initial-segment-ℕ l
pr1 (shift-initial-segment-ℕ I) = subset-initial-segment-ℕ I ∘ succ-ℕ
pr2 (shift-initial-segment-ℕ I) =
  is-initial-segment-initial-segment-ℕ I ∘ succ-ℕ
```

## Properties

### Inhabited initial segments contain `0`

```agda
contains-zero-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x : ℕ) → is-in-initial-segment-ℕ I x → is-in-initial-segment-ℕ I 0
contains-zero-initial-segment-ℕ I zero-ℕ H = H
contains-zero-initial-segment-ℕ I (succ-ℕ x) H =
  is-initial-segment-initial-segment-ℕ I 0
    ( contains-zero-initial-segment-ℕ (shift-initial-segment-ℕ I) x H)
```

### Initial segments that contain a successor contain `1`

```agda
contains-one-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x : ℕ) → is-in-initial-segment-ℕ I (succ-ℕ x) → is-in-initial-segment-ℕ I 1
contains-one-initial-segment-ℕ I =
  contains-zero-initial-segment-ℕ (shift-initial-segment-ℕ I)
```

### Initial segments are closed under `max-ℕ`

```agda
max-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x y : ℕ) → is-in-initial-segment-ℕ I x → is-in-initial-segment-ℕ I y →
  is-in-initial-segment-ℕ I (max-ℕ x y)
max-initial-segment-ℕ I zero-ℕ y H K = K
max-initial-segment-ℕ I (succ-ℕ x) zero-ℕ H K = H
max-initial-segment-ℕ I (succ-ℕ x) (succ-ℕ y) H K =
  max-initial-segment-ℕ (shift-initial-segment-ℕ I) x y H K
```

### The initial segments of numbers less than `n` are finite

Even better, they have count `n+1`.

```agda
[_] : ℕ → initial-segment-ℕ lzero
pr1 [ n ] = λ m → leq-ℕ-Prop m n
pr2 [ n ] m sm≤n = transitive-leq-ℕ m (succ-ℕ m) n sm≤n (succ-leq-ℕ m)

leq-initial-segment-ℕ-set : (n : ℕ) → UU lzero
leq-initial-segment-ℕ-set n = type-subtype (subset-initial-segment-ℕ [ n ])

leq-initial-segment-ℕ-set-to-Fin :
  (n : ℕ) → leq-initial-segment-ℕ-set n → Fin (succ-ℕ n)
leq-initial-segment-ℕ-set-to-Fin n (zero-ℕ , _) = inr star
leq-initial-segment-ℕ-set-to-Fin (succ-ℕ n) (succ-ℕ m , m≤n) =
  inl-Fin (succ-ℕ n) (leq-initial-segment-ℕ-set-to-Fin n (m , m≤n))

leq-initial-segment-ℕ-set-count : (n : ℕ) → count (leq-initial-segment-ℕ-set n)
pr1 (leq-initial-segment-ℕ-set-count n) = succ-ℕ n
pr1 (pr1 (pr2 (leq-initial-segment-ℕ-set-count n)) x) = nat-Fin (succ-ℕ n) x
pr2 (pr1 (pr2 (leq-initial-segment-ℕ-set-count n)) x) = upper-bound-nat-Fin n x
pr1 (pr1 (pr2 (pr2 (leq-initial-segment-ℕ-set-count n)))) =
  leq-initial-segment-ℕ-set-to-Fin n
pr2 (pr1 (pr2 (pr2 (leq-initial-segment-ℕ-set-count n)))) (m , m≤n) =
  eq-type-subtype (λ x → leq-ℕ-Prop x n) {!   !}
pr1 (pr2 (pr2 (pr2 (leq-initial-segment-ℕ-set-count n)))) =
  leq-initial-segment-ℕ-set-to-Fin n
pr2 (pr2 (pr2 (pr2 (leq-initial-segment-ℕ-set-count n)))) (inl x) = {!   !}
pr2 (pr2 (pr2 (pr2 (leq-initial-segment-ℕ-set-count n)))) (inr star) = {!   !}

leq-initial-segment-ℕ-Finite-Type : (n : ℕ) → Finite-Type lzero
pr1 (leq-initial-segment-ℕ-Finite-Type n) = leq-initial-segment-ℕ-set n
pr2 (leq-initial-segment-ℕ-Finite-Type n) =
  unit-trunc-Prop (leq-initial-segment-ℕ-set-count n)
```
