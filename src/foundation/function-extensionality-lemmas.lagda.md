# Function extensionality lemmas

```agda
module foundation.function-extensionality-lemmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.propositions
open import foundation.sections
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

### The space of sections of a propositional bundle is a proposition

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  funext-prop-section-is-prop : is-prop ((a : A) → type-Prop (P a))
  pr1 (funext-prop-section-is-prop f g) =
    eq-htpy λ x → eq-is-prop (is-prop-type-Prop (P x))
  pr2 (funext-prop-section-is-prop f g) eq = lem4 where
    lem1 : (λ x → eq-is-prop (is-prop-type-Prop (P x))) ~ htpy-eq eq
    lem1 x =
      eq-is-contr (is-trunc-is-prop _ (is-prop-type-Prop (P x)) (f x) (g x))

    lem2 : eq-htpy (htpy-eq eq) ＝ eq
    lem2 = is-retraction-eq-htpy' eq

    lem3 :
      eq-htpy (λ x → eq-is-prop (is-prop-type-Prop (P x))) ＝ eq-htpy (htpy-eq eq)
    lem3 = ap eq-htpy (eq-htpy lem1)

    lem4 : eq-htpy (λ x → eq-is-prop (is-prop-type-Prop (P x))) ＝ eq
    lem4 = lem3 ∙ lem2
```
