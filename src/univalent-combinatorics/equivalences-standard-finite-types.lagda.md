# Equivalences between standard finite types

```agda
module univalent-combinatorics.equivalences-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.subtypes
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-unit-type

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.retractions

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We construct **equivalences** between (types built out of)
[standard finite types](univalent-combinatorics.standard-finite-types.md).

### The standard finite types are closed under function types

```agda
function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coproduct unit) ∘e
  ( equiv-is-contr (universal-property-empty' (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( product-Fin (exp-ℕ l k) l) ∘e
  ( equiv-product (function-Fin k l) (equiv-universal-property-unit (Fin l))) ∘e
  ( equiv-universal-property-coproduct (Fin l))

Fin-exp-ℕ : (k l : ℕ) → Fin (exp-ℕ l k) ≃ (Fin k → Fin l)
Fin-exp-ℕ k l = inv-equiv (function-Fin k l)
```

### There are two automorphisms of `Fin 2`, assuming function extensionality

```agda
open import foundation.function-extensionality

flip-map : Fin 2 → Fin 2
flip-map (inl (inr star)) = inr star
flip-map (inr star) = inl (inr star)

flip : Fin 2 ≃ Fin 2
pr1 flip = flip-map
pr1 (pr1 (pr2 flip)) = flip-map
pr2 (pr1 (pr2 flip)) (inl (inr x)) = refl
pr2 (pr1 (pr2 flip)) (inr x) = refl
pr1 (pr2 (pr2 flip)) = flip-map
pr2 (pr2 (pr2 flip)) (inl (inr x)) = refl
pr2 (pr2 (pr2 flip)) (inr x) = refl

Fin-2-equiv-counting : (Fin 2 ≃ Fin 2) → Fin 2
Fin-2-equiv-counting (f , f-is-equiv) with f (inr star)
...                                      | inr star = inr star
...                                      | inl (inr star) = inl (inr star)

count-Fin-2-equiv : count (Fin 2 ≃ Fin 2)
pr1 (count-Fin-2-equiv) = 2
pr1 (pr2 count-Fin-2-equiv) (inl (inr star)) = flip
pr1 (pr2 count-Fin-2-equiv) (inr star) = id-equiv
pr1 (pr1 (pr2 (pr2 count-Fin-2-equiv))) = Fin-2-equiv-counting
pr2 (pr1 (pr2 (pr2 count-Fin-2-equiv))) (f , f-is-equiv) = eq-type-subtype (λ g → is-equiv-Prop g) {!   !}
pr1 (pr2 (pr2 (pr2 count-Fin-2-equiv))) = Fin-2-equiv-counting
pr2 (pr2 (pr2 (pr2 count-Fin-2-equiv))) (inl (inr star)) = refl
pr2 (pr2 (pr2 (pr2 count-Fin-2-equiv))) (inr star) = refl
```
