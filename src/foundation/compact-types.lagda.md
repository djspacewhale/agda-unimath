# Compact types

```agda
module foundation.compact-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.identity-types
open import foundation-core.negation
```

</details>

## Idea

There are several synthetic notions of **compactness** in type theory. The most
straightforward is to say `X` is {{#concept "Σ-compact" Agda=Σ-compact}} when,
for every `p : X → bool`, the type `Σ X λ x → p x ＝ true` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  Σ-compact : UU l
  Σ-compact = (p : X → bool) → is-decidable (Σ X (λ x → p x ＝ true))
```

This definition has the unfortunate defect of being structure rather than a
property; note that `X` could have multiple elements map to `true` under a given
`p`. A good quick fix is to truncate and consider instead the
[existential quantification](foundation.existential-quantification.md) of the
above; this is clearly now a property of `X`, and we call it
{{#concept "∃-compactness" Agda=is-∃-compact}}.

```agda
  is-∃-compact : UU l
  is-∃-compact = (p : X → bool) → is-decidable (type-Prop (∃ X (λ x → Id-Prop bool-Set (p x) true)))

  is-prop-is-decidable-bool : (p : X → bool) → is-prop (is-decidable (type-Prop (∃ X (λ x → Id-Prop bool-Set (p x) true))))
  is-prop-is-decidable-bool p = is-prop-is-decidable (is-prop-exists X λ x → Id-Prop bool-Set (p x) true)

  is-prop-is-∃-compact : is-prop is-∃-compact
  is-prop-is-∃-compact = is-prop-Π-Prop (X → bool) (λ p → is-decidable (type-Prop (∃ X (λ x → Id-Prop bool-Set (p x) true))) , (is-prop-is-decidable-bool p))

∃-Compact-Type : (l : Level) → UU (lsuc l)
∃-Compact-Type l = Σ (UU l) λ X → is-∃-compact X
```

One more notion sees use, which we call
{{#concept "∀'-compactness" Agda=is-∀'-compact}}, and define by substituting
`∀'` for `∃`; that is, `X` is ∀'-compact when it is merely decidable if every
element maps to `true`, versus when such a root merely exists.

```agda
module _
  {l : Level} (X : UU l)
  where

  is-∀'-compact : UU l
  is-∀'-compact = (p : X → bool) → is-decidable (type-Prop (∀' X (λ x → Id-Prop bool-Set (p x) true)))

∀'-Compact-Type : (l : Level) → UU (lsuc l)
∀'-Compact-Type l = Σ (UU l) λ X → is-∀'-compact X
```
