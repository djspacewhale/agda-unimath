# Homomorphisms of abelian groups

```agda
module group-theory.homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.category-of-abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups

open import reflection.erasing-equality
open import reflection.group-solver
```

</details>

## Idea

Homomorphisms between abelian groups are just homomorphisms between their
underlying groups.

## Definition

### The predicate that a map between abelian groups preserves addition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-add-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-add-Ab = preserves-mul-Semigroup (semigroup-Ab A) (semigroup-Ab B)
```

### The predicate that a map between abelian groups preserves zero

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-zero-Ab : (type-Ab A → type-Ab B) → UU l2
  preserves-zero-Ab = preserves-unit-Group (group-Ab A) (group-Ab B)
```

### The predicate that a map between abelian groups preserves negatives

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-negatives-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-negatives-Ab =
    preserves-inverses-Group (group-Ab A) (group-Ab B)
```

### Homomorphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  hom-set-Ab : Set (l1 ⊔ l2)
  hom-set-Ab = hom-set-Large-Category Ab-Large-Category A B

  hom-Ab : UU (l1 ⊔ l2)
  hom-Ab = hom-Large-Category Ab-Large-Category A B

  map-hom-Ab : hom-Ab → type-Ab A → type-Ab B
  map-hom-Ab = map-hom-Group (group-Ab A) (group-Ab B)

  preserves-add-hom-Ab : (f : hom-Ab) → preserves-add-Ab A B (map-hom-Ab f)
  preserves-add-hom-Ab f = preserves-mul-hom-Group (group-Ab A) (group-Ab B) f

  preserves-zero-hom-Ab : (f : hom-Ab) → preserves-zero-Ab A B (map-hom-Ab f)
  preserves-zero-hom-Ab f = preserves-unit-hom-Group (group-Ab A) (group-Ab B) f

  preserves-negatives-hom-Ab :
    (f : hom-Ab) → preserves-negatives-Ab A B (map-hom-Ab f)
  preserves-negatives-hom-Ab f =
    preserves-inv-hom-Group (group-Ab A) (group-Ab B) f

  hom-semigroup-hom-Ab :
    hom-Ab → hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
  pr1 (hom-semigroup-hom-Ab f) = map-hom-Ab f
  pr2 (hom-semigroup-hom-Ab f) = preserves-add-hom-Ab f

  hom-commutative-monoid-hom-Ab :
    hom-Ab →
    hom-Commutative-Monoid
      ( commutative-monoid-Ab A)
      ( commutative-monoid-Ab B)
  pr1 (hom-commutative-monoid-hom-Ab f) = hom-semigroup-hom-Ab f
  pr2 (hom-commutative-monoid-hom-Ab f) = preserves-zero-hom-Ab f
```

### Characterization of the identity type of the abelian group homomorphisms

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  htpy-hom-Ab : (f g : hom-Ab A B) → UU (l1 ⊔ l2)
  htpy-hom-Ab f g = htpy-hom-Group (group-Ab A) (group-Ab B) f g

  refl-htpy-hom-Ab : (f : hom-Ab A B) → htpy-hom-Ab f f
  refl-htpy-hom-Ab f = refl-htpy-hom-Group (group-Ab A) (group-Ab B) f

  htpy-eq-hom-Ab : (f g : hom-Ab A B) → Id f g → htpy-hom-Ab f g
  htpy-eq-hom-Ab f g = htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  abstract
    is-torsorial-htpy-hom-Ab :
      (f : hom-Ab A B) → is-torsorial (htpy-hom-Ab f)
    is-torsorial-htpy-hom-Ab f =
      is-torsorial-htpy-hom-Group (group-Ab A) (group-Ab B) f

  abstract
    is-equiv-htpy-eq-hom-Ab :
      (f g : hom-Ab A B) → is-equiv (htpy-eq-hom-Ab f g)
    is-equiv-htpy-eq-hom-Ab f g =
      is-equiv-htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  eq-htpy-hom-Ab : {f g : hom-Ab A B} → htpy-hom-Ab f g → Id f g
  eq-htpy-hom-Ab = eq-htpy-hom-Group (group-Ab A) (group-Ab B)

  is-set-hom-Ab : is-set (hom-Ab A B)
  is-set-hom-Ab = is-set-hom-Group (group-Ab A) (group-Ab B)
```

### The identity morphism of abelian groups

```agda
preserves-add-id : {l : Level} (A : Ab l) → preserves-add-Ab A A id
preserves-add-id A = preserves-mul-id-Semigroup (semigroup-Ab A)

id-hom-Ab : {l1 : Level} (A : Ab l1) → hom-Ab A A
id-hom-Ab A = id-hom-Group (group-Ab A)
```

### Composition of morphisms of abelian groups

```agda
comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( hom-Ab B C) → (hom-Ab A B) → (hom-Ab A C)
comp-hom-Ab A B C =
  comp-hom-Group (group-Ab A) (group-Ab B) (group-Ab C)
```

### Associativity of composition of morphisms of abelian groups

```agda
associative-comp-hom-Ab :
  {l1 l2 l3 l4 : Level}
  (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4)
  (h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  comp-hom-Ab A B D (comp-hom-Ab B C D h g) f ＝
  comp-hom-Ab A C D h (comp-hom-Ab A B C g f)
associative-comp-hom-Ab A B C D =
  associative-comp-hom-Semigroup
    ( semigroup-Ab A)
    ( semigroup-Ab B)
    ( semigroup-Ab C)
    ( semigroup-Ab D)
```

### The unit laws for composition of abelian groups

```agda
left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab A B =
  left-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab A B =
  right-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
```

### A group `G` is abelian iff `λ g → inv-Group G g` is a homomorphism

```agda
module _
  {l : Level} (G : Group l)
  where

  inv-map-Group : type-Group G → type-Group G
  inv-map-Group g = inv-Group G g

  is-abelian-is-hom-inv-map-Group : is-abelian-Group G → preserves-mul-Group G G inv-map-Group
  is-abelian-is-hom-inv-map-Group G-ab {x} {y} =
    equational-reasoning
      inv-map-Group (mul-Group G x y) ＝ mul-Group G (inv-Group G y) (inv-Group G x)
        by distributive-inv-mul-Group G
      ＝ mul-Group G (inv-map-Group x) (inv-map-Group y)
        by G-ab (inv-Group G y) (inv-Group G x)

  is-hom-inv-map-Group-is-abelian : preserves-mul-Group G G inv-map-Group → is-abelian-Group G
  is-hom-inv-map-Group-is-abelian inv-hom x y =
    equational-reasoning
      mul-Group G x y ＝ mul-Group G (inv-Group G (inv-Group G x)) (inv-Group G (inv-Group G y))
        by inv (ap-binary (mul-Group G) (inv-inv-Group G x) (inv-inv-Group G y))
      ＝ inv-Group G (mul-Group G (inv-Group G y) (inv-Group G x))
        by inv (distributive-inv-mul-Group G)
      ＝ mul-Group G (inv-Group G (inv-Group G y)) (inv-Group G (inv-Group G x))
        by inv-hom
      ＝ mul-Group G y x
        by ap-binary (mul-Group G) (inv-inv-Group G y) (inv-inv-Group G x)

  is-abelian-iff-is-hom-inv-Group : is-abelian-Group G ↔ preserves-mul-Group G G inv-map-Group
  pr1 is-abelian-iff-is-hom-inv-Group = is-abelian-is-hom-inv-map-Group
  pr2 is-abelian-iff-is-hom-inv-Group = is-hom-inv-map-Group-is-abelian

neg-hom-Ab' : {l : Level} (A : Ab l) → hom-Ab A A
neg-hom-Ab' A = (neg-Ab A) , is-abelian-is-hom-inv-map-Group (group-Ab A) (commutative-add-Ab A)
```

### The abelian group of homomorphisms `G → H`

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (H : Ab l2)
  where

  zero-hom-Ab : hom-Ab G H
  pr1 zero-hom-Ab = λ _ → zero-Ab H
  pr2 zero-hom-Ab {x} {y} = inv (left-unit-law-add-Ab H (pr1 zero-hom-Ab (add-Ab G x y)))

  neg-hom-Ab : hom-Ab G H → hom-Ab G H
  pr1 (neg-hom-Ab f) x = neg-Ab H (map-hom-Ab G H f x)
  pr2 (neg-hom-Ab (f , f-preserves-add)) {x} {y} = equational-reasoning
    pr1 (neg-hom-Ab (f , f-preserves-add)) (add-Ab G x y) ＝ neg-Ab H (add-Ab H (f x) (f y))
      by ap (neg-Ab H) f-preserves-add
    ＝ add-Ab H (pr1 (neg-hom-Ab (f , f-preserves-add)) x) (pr1 (neg-hom-Ab (f , f-preserves-add)) y)
      by is-abelian-is-hom-inv-map-Group (group-Ab H) (commutative-add-Ab H)

  add-map-Ab : hom-Ab G H → hom-Ab G H → hom-Ab G H
  pr1 (add-map-Ab f g) x = add-Ab H (map-hom-Ab G H f x) (map-hom-Ab G H g x)
  pr2 (add-map-Ab (f , f-preserves-add) (g , g-preserves-add)) {x} {y} = equational-reasoning
    pr1 (add-map-Ab (f , f-preserves-add) (g , g-preserves-add)) (add-Ab G x y) ＝ add-Ab H (add-Ab H (f x) (f y)) (add-Ab H (g x) (g y))
      by ap-add-Ab H f-preserves-add g-preserves-add
    ＝ add-Ab H (pr1 (add-map-Ab (f , f-preserves-add) (g , g-preserves-add)) x) (pr1 (add-map-Ab (f , f-preserves-add) (g , g-preserves-add)) y)
      by {!   !}

  semigroup-hom-Ab : Semigroup (l1 ⊔ l2)
  pr1 semigroup-hom-Ab = hom-set-Ab G H
  pr1 (pr2 semigroup-hom-Ab) = add-map-Ab
  pr2 (pr2 semigroup-hom-Ab) f g h = eq-htpy-hom-Ab G H λ x → pr2 (pr2 (pr1 (pr1 H))) (pr1 f x) (pr1 g x) (pr1 h x)

  group-hom-Ab : Group (l1 ⊔ l2)
  pr1 group-hom-Ab = semigroup-hom-Ab
  pr1 (pr1 (pr2 group-hom-Ab)) = zero-hom-Ab
  pr1 (pr2 (pr1 (pr2 group-hom-Ab))) f = eq-htpy-hom-Ab G H (λ x → pr1 (pr2 (pr1 (pr2 (pr1 H)))) (pr1 f x))
  pr2 (pr2 (pr1 (pr2 group-hom-Ab))) f = eq-htpy-hom-Ab G H (λ x → pr2 (pr2 (pr1 (pr2 (pr1 H)))) (pr1 f x))
  pr1 (pr2 (pr2 group-hom-Ab)) = neg-hom-Ab
  pr1 (pr2 (pr2 (pr2 group-hom-Ab))) f = eq-htpy-hom-Ab G H (λ x → pr1 (pr2 (pr2 (pr2 (pr1 H)))) (pr1 f x))
  pr2 (pr2 (pr2 (pr2 group-hom-Ab))) f = eq-htpy-hom-Ab G H (λ x → pr2 (pr2 (pr2 (pr2 (pr1 H)))) (pr1 f x))

  ab-hom-Ab : Ab (l1 ⊔ l2)
  pr1 ab-hom-Ab = group-hom-Ab
  pr2 ab-hom-Ab f g = eq-htpy-hom-Ab G H (λ x → pr2 H (pr1 f x) (pr1 g x))
```
