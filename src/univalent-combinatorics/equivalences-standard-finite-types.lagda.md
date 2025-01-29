# Equivalences between standard finite types

```agda
module univalent-combinatorics.equivalences-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
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
