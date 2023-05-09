# Sort by insertion for vectors

```agda
module lists.sort-by-insertion-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors
open import lists.sorted-vectors
open import lists.sorting-algorithms-vectors

open import order-theory.decidable-total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Sort by insertion is a recursive sort on vectors. If a vector is empty or with
only one element then it is sorted. Otherwise, we recursively sort the tail of
the vector. Then we compare the head of the vector to the head of the sorted
tail. If the head is less or equal than the head of the tail the vector is
sorted. Otherwise we permute the two elements and we recursively sort the tail
of the vector.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  helper-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : vec (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ (n)))
  helper-insertion-sort-vec x y l (inl p) = x ∷ y ∷ l
  helper-insertion-sort-vec {0} x y empty-vec (inr p) = y ∷ x ∷ empty-vec
  helper-insertion-sort-vec {succ-ℕ n} x y (z ∷ l) (inr p) =
    y ∷
    ( helper-insertion-sort-vec
      ( x)
      ( z)
      ( l)
      ( is-leq-or-strict-greater-Decidable-Total-Order X x z))

  insertion-sort-vec :
    {n : ℕ} →
    vec (type-Decidable-Total-Order X) n →
    vec (type-Decidable-Total-Order X) n
  insertion-sort-vec {zero-ℕ} empty-vec = empty-vec
  insertion-sort-vec {1} l = l
  insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    helper-insertion-sort-vec
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ l)))
      ( tail-vec (insertion-sort-vec (y ∷ l)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)
```

## Properties

### Sort by insertion is a permutation

```agda
  helper-permutation-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : vec (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    Permutation (succ-ℕ (succ-ℕ (n)))
  helper-permutation-insertion-sort-vec x y l (inl _) = id-equiv
  helper-permutation-insertion-sort-vec {0} x y empty-vec (inr _) =
    swap-two-last-elements-transposition-Fin 0
  helper-permutation-insertion-sort-vec {succ-ℕ n} x y (z ∷ l) (inr _) =
    ( ( swap-two-last-elements-transposition-Fin (succ-ℕ n)) ∘e
      ( ( equiv-coprod
          ( helper-permutation-insertion-sort-vec
            ( x)
            ( z)
            ( l)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( id-equiv))))

  permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    Permutation n
  permutation-insertion-sort-vec {zero-ℕ} empty-vec = id-equiv
  permutation-insertion-sort-vec {1} l = id-equiv
  permutation-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    equiv-coprod
      ( permutation-insertion-sort-vec (y ∷ l))
      ( id-equiv) ∘e
    helper-permutation-insertion-sort-vec
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ l)))
      ( tail-vec (insertion-sort-vec (y ∷ l)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)

  helper-is-permutation-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n)
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    helper-insertion-sort-vec x y v p ＝
    permute-vec
      ( succ-ℕ (succ-ℕ n))
      ( x ∷ y ∷ v)
      ( helper-permutation-insertion-sort-vec x y v p)
  helper-is-permutation-insertion-sort-vec x y v (inl _) =
    inv (compute-permute-vec-id-equiv (succ-ℕ (succ-ℕ _)) (x ∷ y ∷ v))
  helper-is-permutation-insertion-sort-vec {zero-ℕ} x y empty-vec (inr _) =
    refl
  helper-is-permutation-insertion-sort-vec {succ-ℕ n} x y (z ∷ v) (inr p) =
    eq-Eq-vec
      ( succ-ℕ (succ-ℕ (succ-ℕ n)))
      ( helper-insertion-sort-vec x y (z ∷ v) (inr p))
      ( permute-vec
        ( succ-ℕ (succ-ℕ (succ-ℕ n)))
        ( x ∷ y ∷ z ∷ v)
        ( helper-permutation-insertion-sort-vec x y (z ∷ v) (inr p)))
      ( refl ,
        Eq-eq-vec
          ( succ-ℕ (succ-ℕ n))
          ( helper-insertion-sort-vec
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( tail-vec
            ( permute-vec
              ( succ-ℕ (succ-ℕ (succ-ℕ n)))
              ( x ∷ y ∷ z ∷ v)
              ( helper-permutation-insertion-sort-vec x y (z ∷ v) (inr p))))
          ( ( helper-is-permutation-insertion-sort-vec
              ( x)
              ( z)
              ( v)
              ( is-leq-or-strict-greater-Decidable-Total-Order X x z)) ∙
            ( ap
              ( tail-vec)
              ( ap-permute-vec
                ( equiv-coprod
                  ( helper-permutation-insertion-sort-vec
                    ( x)
                    ( z)
                    ( v)
                    ( is-leq-or-strict-greater-Decidable-Total-Order
                      ( X)
                      ( x)
                      ( z)))
                  ( id-equiv))
                ( inv
                  ( compute-swap-two-last-elements-transposition-Fin-permute-vec
                    (succ-ℕ n)
                    ( z ∷ v)
                    ( x)
                    ( y))) ∙
                ( inv
                  ( compute-composition-permute-vec
                    (succ-ℕ (succ-ℕ (succ-ℕ n)))
                    ( x ∷ y ∷ z ∷ v)
                    ( swap-two-last-elements-transposition-Fin (succ-ℕ n))
                    ( equiv-coprod
                      ( helper-permutation-insertion-sort-vec
                        ( x)
                        ( z)
                        ( v)
                        ( is-leq-or-strict-greater-Decidable-Total-Order
                          ( X)
                          ( x)
                          ( z)))
                        ( id-equiv))))))))

  is-permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    insertion-sort-vec v ＝ permute-vec n v (permutation-insertion-sort-vec v)
  is-permutation-insertion-sort-vec {0} empty-vec = refl
  is-permutation-insertion-sort-vec {1} (x ∷ empty-vec) = refl
  is-permutation-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    ( ( helper-is-permutation-insertion-sort-vec
        ( x)
        ( head-vec (insertion-sort-vec (y ∷ v)))
        ( tail-vec (insertion-sort-vec (y ∷ v)))
        ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)) ∙
      ( ( ap-permute-vec
          ( helper-permutation-insertion-sort-vec
            ( x)
            ( head-vec (insertion-sort-vec (y ∷ v)))
            ( tail-vec (insertion-sort-vec (y ∷ v)))
            ( is-leq-or-strict-greater-Decidable-Total-Order X _ _))
          ( ap
            ( λ l → x ∷ l)
            ( cons-head-tail-vec n (insertion-sort-vec (y ∷ v)) ∙
              is-permutation-insertion-sort-vec (y ∷ v)))) ∙
        ( ( inv
            ( compute-composition-permute-vec
              (succ-ℕ (succ-ℕ n))
              ( x ∷ y ∷ v)
              ( equiv-coprod
                ( permutation-insertion-sort-vec (y ∷ v))
                ( id-equiv))
              ( helper-permutation-insertion-sort-vec
                ( x)
                ( head-vec (insertion-sort-vec (y ∷ v)))
                ( tail-vec (insertion-sort-vec (y ∷ v)))
                ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)))))))
```

### Sort by insertion is sorting vectors

```agda
  helper-is-sorting-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n) →
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    is-sorted-vec X (y ∷ v) →
    is-sorted-vec X (helper-insertion-sort-vec x y v p)
  helper-is-sorting-insertion-sort-vec {0} x y empty-vec (inl p) _ =
    p , raise-star
  helper-is-sorting-insertion-sort-vec {0} x y empty-vec (inr p) _ =
    pr2 p , raise-star
  helper-is-sorting-insertion-sort-vec {succ-ℕ n} x y l (inl p) s =
    p , s
  helper-is-sorting-insertion-sort-vec {succ-ℕ n} x y (z ∷ v) (inr p) s =
    is-sorted-vec-is-sorted-least-element-vec
      ( X)
      ( helper-insertion-sort-vec x y (z ∷ v) (inr p))
      ( tr
        ( λ l → is-least-element-vec X y l)
        ( inv
          ( helper-is-permutation-insertion-sort-vec
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z)))
        ( is-least-element-permute-vec
          ( X)
          ( y)
          ( x ∷ z ∷ v)
          ( helper-permutation-insertion-sort-vec
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( pr2 p ,
            pr1
              ( is-sorted-least-element-vec-is-sorted-vec
                ( X)
                ( y ∷ z ∷ v)
                ( s)))) ,
         is-sorted-least-element-vec-is-sorted-vec
           ( X)
           ( helper-insertion-sort-vec
             ( x)
             ( z)
             ( v)
             ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
           ( helper-is-sorting-insertion-sort-vec
             ( x)
             ( z)
             ( v)
             ( is-leq-or-strict-greater-Decidable-Total-Order X x z)
             ( is-sorted-tail-is-sorted-vec X (y ∷ z ∷ v) s)))

  is-sorting-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-vec X (insertion-sort-vec v)
  is-sorting-insertion-sort-vec {0} v = raise-star
  is-sorting-insertion-sort-vec {1} v = raise-star
  is-sorting-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    helper-is-sorting-insertion-sort-vec
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ v)))
      ( tail-vec (insertion-sort-vec (y ∷ v)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)
      ( tr
        ( λ l → is-sorted-vec X l)
        ( inv (cons-head-tail-vec n (insertion-sort-vec (y ∷ v))))
        ( is-sorting-insertion-sort-vec (y ∷ v)))
```

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-vec :
    is-sort-vec X (insertion-sort-vec)
  pr1 (pr1 (is-sort-insertion-sort-vec n)) = permutation-insertion-sort-vec
  pr2 (pr1 (is-sort-insertion-sort-vec n)) = is-permutation-insertion-sort-vec
  pr2 (is-sort-insertion-sort-vec n) = is-sorting-insertion-sort-vec
```