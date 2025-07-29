# Graded abelian groups

```agda
module homological-algebra.graded-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.universe-levels

open import group-theory.abelian-groups
```

</details

## Idea

A {{concept "graded abelian group" Agda=graded-Ab}} is a ℤ-indexed family of
[abelian groups](group-theory.abelian-groups.md).

As graded abelian groups are an infinitary structure, issues of predicativity
arise. What we define in this module may be considered "small graded abelian
groups", while polymorphic/impredicative graded abelian groups will be defined
elsewhere.

```agda
graded-Ab : (l : Level) → UU (lsuc l)
graded-Ab l = ℤ → Ab l
```
