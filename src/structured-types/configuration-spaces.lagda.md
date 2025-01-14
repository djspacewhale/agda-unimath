# Configuration spaces

```agda
module structured-types.configuration-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.strongly-extensional-maps
open import foundation.strongly-injective-maps
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.concrete-groups
open import group-theory.concrete-group-actions
open import group-theory.orbits-concrete-group-actions
open import group-theory.symmetric-concrete-groups

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

## Idea

For a type `X` with a
[tight apartness relation](foundation.apartness-relations.md) `_#_`, the
**`n`'th ordered configuration space** of `X` is, equivalently, the type of
[strongly injective maps](foundation.strongly-injective-maps) from `Fin n` to
`X`.

## Definition

```agda
Conf :
  {l1 l2 : Level} (n : ℕ) (X : Type-With-Tight-Apartness l1 l2) → UU (l1 ⊔ l2)
Conf n X = Strong-Injection (Fin-Type-With-Tight-Apartness n) X

Conf-is-set :
  {l1 l2 : Level} (n : ℕ) (X : Type-With-Tight-Apartness l1 l2) → is-set (Conf n X)
Conf-is-set n X (f , ext-f , inj-f) (.f , .ext-f , .inj-f) refl q = {!   !}
```

There is a natural action of the
[symmetric group](group-theory.symmetric-concrete-groups.md) of `Fin n` on
`Conf n X` by permuting the arguments of a given strong injection; the
[orbit space](group-theory.orbits-concrete-group-actions.md) of this action is
the **`n`'th unordered configuration space** of `X`.

```agda
sym-Fin-action-Conf :
  {l1 l2 : Level} (n : ℕ) (X : Type-With-Tight-Apartness l1 l2) → action-Concrete-Group (l1 ⊔ l2) (symmetric-Concrete-Group (Fin-Set n))
sym-Fin-action-Conf n X ((Y , p) , f) = (Conf n X) , (Conf-is-set n X)

UConf :
  {l1 l2 : Level} (n : ℕ) (X : Type-With-Tight-Apartness l1 l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
UConf n X =
  orbit-action-Concrete-Group (symmetric-Concrete-Group (Fin-Set n)) (sym-Fin-action-Conf n X)
```
