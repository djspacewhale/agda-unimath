# Projective line over a ring

```agda
module ring-theory.projective-line-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations

open import ring-theory.commutative-rings
open import ring-theory.groups-of-units-rings
```

</details>

## Idea

The **projective line** over a [ring](ring-theory.rings.md) `R` is the set of
"projective coordinates" over `R`. These are ordered pairs `(r,s)` from `R`
modulo mere existence of a `u : type-group-of-units-Ring R` such that
`u * r ＝ r'` and `u * s = s'`, say.

## Definition

### Projective lines

```agda
module _
  {l : Level} (R : Ring l)
  where
```
