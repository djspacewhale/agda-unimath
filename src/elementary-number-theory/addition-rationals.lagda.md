---
title: Addition on the rationals
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.addition-rationals where

open import elementary-number-theory.addition-integers using
  ( add-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-mul-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ)
open import elementary-number-theory.rational-numbers using
  ( ℚ; zero-ℚ; in-fraction-ℤ; is-prop-is-reduced-fraction-ℤ )

open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equational-reasoning
open import foundation.identity-types using
  (_＝_; refl; _∙_; inv; ap; ap-binary)
open import foundation.propositions using (eq-is-prop)

open import structured-types.pointed-types-equipped-with-automorphisms
```

## Idea

We introduce addition on the rationals and derive its basic properties. Properties of addition with respect to inequality are derived in `inequality-ratonals`.

## Definition

```agda
add-ℚ : ℚ → ℚ → ℚ
add-ℚ (pair (pair m (pair n (n-pos))) p) (pair (pair m' (pair n' (n'-pos))) p') =
  in-fraction-ℤ
    ( pair (add-ℤ (mul-ℤ m n') (mul-ℤ m' n))
    ( pair (mul-ℤ n n') (is-positive-mul-ℤ n-pos n'-pos)))

add-ℚ' : ℚ → ℚ → ℚ
add-ℚ' x y = add-ℚ y x

infix 30 _+ℚ_
_+ℚ_ = add-ℚ

ap-add-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → add-ℚ x y ＝ add-ℚ x' y'
ap-add-ℚ p q = ap-binary add-ℚ p q
```

## Properties

### Unit laws

```agda
-- abstract
  -- left-unit-law-add-ℚ : (k : ℚ) → zero-ℚ +ℚ k ＝ k
  -- left-unit-law-add-ℚ k =
  --   eq-pair-Σ
  --     ( {!!} )
  --     ( eq-is-prop (is-prop-is-reduced-fraction-ℤ (pr1 k)))

--   right-unit-law-add-ℚ : (k : ℚ) → ℚ +ℚ zero-ℚ ＝ k
```