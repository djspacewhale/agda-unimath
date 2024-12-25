# Configuration spaces

```agda
module structured-types.configuration-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.universe-levels
```

## Idea

For a type `X` with an [apartness relation](foundation.apartness-relations.md)
`_#_`, the **n'th ordered configuration space** of `X` is, equivalently, the
type of [strongly extensional maps](foundation.strongly-extensional-maps)
