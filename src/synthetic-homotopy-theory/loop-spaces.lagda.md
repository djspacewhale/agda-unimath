# Loop spaces

```agda
module synthetic-homotopy-theory.loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.wild-monoids
open import structured-types.wild-quasigroups
open import structured-types.wild-groups
```

</details>

## Idea

The **loop space** of a [pointed type](structured-types.pointed-types.md) `A` is
the pointed type of self-[identifications](foundation-core.identity-types.md) of
the base point of `A`. The loop space comes equipped with a group-like structure
induced by the groupoidal-like structure on identifications.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The loop space of a pointed type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Ω : UU l
  type-Ω = Id (point-Pointed-Type A) (point-Pointed-Type A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = pair type-Ω refl-Ω
```

### The magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω x y = x ∙ y

  Ω-Magma : Magma l
  pr1 Ω-Magma = type-Ω A
  pr2 Ω-Magma = mul-Ω
```

### The H-space of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  left-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A (refl-Ω A) x ＝ x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A x (refl-Ω A) ＝ x
  right-unit-law-mul-Ω x = right-unit

  coherence-unit-laws-mul-Ω :
    left-unit-law-mul-Ω refl ＝ right-unit-law-mul-Ω refl
  coherence-unit-laws-mul-Ω = refl

  Ω-H-Space : H-Space l
  pr1 Ω-H-Space = Ω A
  pr1 (pr2 Ω-H-Space) = mul-Ω A
  pr1 (pr2 (pr2 Ω-H-Space)) = left-unit-law-mul-Ω
  pr1 (pr2 (pr2 (pr2 Ω-H-Space))) = right-unit-law-mul-Ω
  pr2 (pr2 (pr2 (pr2 Ω-H-Space))) = coherence-unit-laws-mul-Ω
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = inv

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (inv-Ω x) x) (refl-Ω A)
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (inv-Ω x)) (refl-Ω A)
  right-inverse-law-mul-Ω x = right-inv x

  Ω-Wild-Quasigroup : Wild-Quasigroup l
  pr1 Ω-Wild-Quasigroup = Ω-Magma A
  pr2 Ω-Wild-Quasigroup = is-binary-equiv-concat
```

### Associativity of concatenation on loop spaces

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  associative-mul-Ω :
    (x y z : type-Ω A) →
    Id (mul-Ω A (mul-Ω A x y) z) (mul-Ω A x (mul-Ω A y z))
  associative-mul-Ω x y z = assoc x y z
```

### The wild monoid and group of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  is-unital-associator-Ω : is-unital-associator (Ω-H-Space A) (associative-mul-Ω A)
  pr1 is-unital-associator-Ω y z = refl
  pr1 (pr2 is-unital-associator-Ω) = coherence-one
  pr1 (pr2 (pr2 is-unital-associator-Ω)) b y = coherence-two b y
  pr2 (pr2 (pr2 is-unital-associator-Ω)) = star

  Ω-Wild-Monoid : Wild-Monoid l
  pr1 Ω-Wild-Monoid = Ω-H-Space A
  pr1 (pr2 Ω-Wild-Monoid) = associative-mul-Ω A
  pr2 (pr2 Ω-Wild-Monoid) = is-unital-associator-Ω

  equiv-left-comp-inv-Ω : (a b : type-Ω A) → mul-Ω A (mul-Ω A (inv-Ω A a) a) b ＝ b
  equiv-left-comp-inv-Ω a b = inv (equiv-left-comp-inv a b)

  equiv-right-comp-inv-Ω : (a b : type-Ω A) → mul-Ω A (mul-Ω A a b) (inv-Ω A b) ＝ a
  equiv-right-comp-inv-Ω a b = inv (equiv-right-comp-inv a b ∙ inv (assoc a b (inv b)))

  mul-Ω-binary-equiv : is-binary-equiv (mul-Ω A)
  mul-Ω-binary-equiv = is-binary-equiv-concat

  Ω-Wild-Group : Wild-Group l
  pr1 Ω-Wild-Group = Ω-Wild-Monoid
  pr2 Ω-Wild-Group = mul-Ω-binary-equiv
```

We compute transport of `type-Ω`.

```agda
module _
  {l1 : Level} {A : UU l1} {x y : A}
  where

  equiv-tr-Ω : Id x y → Ω (pair A x) ≃∗ Ω (pair A y)
  equiv-tr-Ω refl = pair id-equiv refl

  equiv-tr-type-Ω : Id x y → type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (equiv-tr-Ω p)

  tr-type-Ω : Id x y → type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  is-equiv-tr-type-Ω : (p : Id x y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : Id x y) → Id (tr-type-Ω p refl) refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : Id x y) (u v : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (mul-Ω (pair A x) u v))
      ( mul-Ω (pair A y) (tr-type-Ω p u) (tr-type-Ω p v))
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : Id x y) (u : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (inv-Ω (pair A x) u))
      ( inv-Ω (pair A y) (tr-type-Ω p u))
  preserves-inv-tr-Ω refl u = refl

  eq-tr-type-Ω :
    (p : Id x y) (q : type-Ω (pair A x)) →
    Id (tr-type-Ω p q) (inv p ∙ (q ∙ p))
  eq-tr-type-Ω refl q = inv right-unit
```

## Properties

### Every pointed identity type is equivalent to a loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-loop-pointed-identity :
    ( pair (point-Pointed-Type A ＝ x) p) ≃∗ Ω A
  pr1 pointed-equiv-loop-pointed-identity =
    equiv-concat' (point-Pointed-Type A) (inv p)
  pr2 pointed-equiv-loop-pointed-identity =
    right-inv p
```

### The wild group of pointed maps into a loop space, assuming function extensionality

```agda
open import foundation.function-extensionality

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  Ω-mapping-unit : A →∗ Ω B
  Ω-mapping-unit = (λ x → refl-Ω B) , refl

  Ω-mapping-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  Ω-mapping-Pointed-Type = A →∗ Ω B , zero-pointed-map A (Ω B)

  Ω-mapping-type : UU (l1 ⊔ l2)
  Ω-mapping-type = type-Pointed-Type Ω-mapping-Pointed-Type

  mul-Ω-mapping-type : Ω-mapping-type → Ω-mapping-type → Ω-mapping-type
  pr1 (mul-Ω-mapping-type (f , p) (g , q)) x = mul-Ω B (f x) (g x)
  pr2 (mul-Ω-mapping-type (f , p) (g , q)) = ap-binary (mul-Ω B) p q

  left-unit-law-mul-Ω-mapping : (f : Ω-mapping-type) → mul-Ω-mapping-type Ω-mapping-unit f ＝ f
  left-unit-law-mul-Ω-mapping f = eq-pointed-htpy (mul-Ω-mapping-type Ω-mapping-unit f) f htp where
    htp : mul-Ω-mapping-type Ω-mapping-unit f ~∗ f
    pr1 htp x = left-unit-law-mul-Ω B (map-pointed-map f x)
    pr2 htp = ap-eq-htpy (λ x → refl ∙ x) (λ x → x) (λ x → left-unit-law-mul-Ω B x) ∙ htp2 where
      htp2 : ap (λ x → x) (pr2 f) ∙ refl ＝ pr2 f
      htp2 = right-unit ∙ ap-id (preserves-point-pointed-map f)

  right-unit-law-mul-Ω-mapping : (f : Ω-mapping-type) → mul-Ω-mapping-type f Ω-mapping-unit ＝ f
  right-unit-law-mul-Ω-mapping f = eq-pointed-htpy (mul-Ω-mapping-type f Ω-mapping-unit) f htp where
    htp : mul-Ω-mapping-type f Ω-mapping-unit ~∗ f
    pr1 htp x = right-unit-law-mul-Ω B (map-pointed-map f x)
    pr2 htp = {!   !} ∙ {!   !}

  unit-law-coherence-Ω-mapping : left-unit-law-mul-Ω-mapping (zero-pointed-map A (Ω B)) ＝ right-unit-law-mul-Ω-mapping (zero-pointed-map A (Ω B))
  unit-law-coherence-Ω-mapping = {!   !}

  Ω-mapping-H-Space : H-Space (l1 ⊔ l2)
  pr1 Ω-mapping-H-Space = Ω-mapping-Pointed-Type
  pr1 (pr2 Ω-mapping-H-Space) = mul-Ω-mapping-type
  pr1 (pr2 (pr2 Ω-mapping-H-Space)) = left-unit-law-mul-Ω-mapping
  pr1 (pr2 (pr2 (pr2 Ω-mapping-H-Space))) = right-unit-law-mul-Ω-mapping
  pr2 (pr2 (pr2 (pr2 Ω-mapping-H-Space))) = unit-law-coherence-Ω-mapping

  associator-Ω-mapping : (f g h : Ω-mapping-type) → mul-Ω-mapping-type (mul-Ω-mapping-type f g) h ＝ mul-Ω-mapping-type f (mul-Ω-mapping-type g h)
  associator-Ω-mapping f g h = eq-pointed-htpy (mul-Ω-mapping-type (mul-Ω-mapping-type f g) h) (mul-Ω-mapping-type f (mul-Ω-mapping-type g h)) htp where
    htp : mul-Ω-mapping-type (mul-Ω-mapping-type f g) h ~∗ mul-Ω-mapping-type f (mul-Ω-mapping-type g h)
    pr1 htp x = associative-mul-Ω B (map-pointed-map f x) (map-pointed-map g x) (map-pointed-map h x)
    pr2 htp = {!   !} ∙ {!   !}

  is-unital-associator-Ω-mapping : is-unital-associator Ω-mapping-H-Space associator-Ω-mapping
  pr1 is-unital-associator-Ω-mapping y z = {!   !}
  pr1 (pr2 is-unital-associator-Ω-mapping) x z = {!   !}
  pr1 (pr2 (pr2 is-unital-associator-Ω-mapping)) x y = {!   !}
  pr2 (pr2 (pr2 is-unital-associator-Ω-mapping)) = star

  Ω-mapping-Wild-Monoid : Wild-Monoid (l1 ⊔ l2)
  pr1 Ω-mapping-Wild-Monoid = Ω-mapping-H-Space
  pr2 Ω-mapping-Wild-Monoid = associator-Ω-mapping , is-unital-associator-Ω-mapping

  inv-Ω-mapping : Ω-mapping-type → Ω-mapping-type
  pr1 (inv-Ω-mapping f) x = inv-Ω B (map-pointed-map f x)
  pr2 (inv-Ω-mapping f) = ap (inv-Ω B) (preserves-point-pointed-map f)

  left-equiv-mul-Ω-mapping : (f : Ω-mapping-type) → is-equiv (λ g → mul-Ω-mapping-type g f)
  pr1 (pr1 (left-equiv-mul-Ω-mapping f)) g = mul-Ω-mapping-type g (inv-Ω-mapping f)
  pr2 (pr1 (left-equiv-mul-Ω-mapping f)) g = {!   !}
  pr1 (pr2 (left-equiv-mul-Ω-mapping f)) g = mul-Ω-mapping-type g (inv-Ω-mapping f)
  pr2 (pr2 (left-equiv-mul-Ω-mapping f)) g = {!   !}

  right-equiv-mul-Ω-mapping : (f : Ω-mapping-type) → is-equiv (λ g → mul-Ω-mapping-type f g)
  pr1 (pr1 (right-equiv-mul-Ω-mapping f)) g = mul-Ω-mapping-type (inv-Ω-mapping f) g
  pr2 (pr1 (right-equiv-mul-Ω-mapping f)) g = {!   !}
  pr1 (pr2 (right-equiv-mul-Ω-mapping f)) g = mul-Ω-mapping-type (inv-Ω-mapping f) g
  pr2 (pr2 (right-equiv-mul-Ω-mapping f)) g = {!   !}

  is-binary-equiv-mul-Ω-mapping : is-binary-equiv mul-Ω-mapping-type
  pr1 is-binary-equiv-mul-Ω-mapping = left-equiv-mul-Ω-mapping
  pr2 is-binary-equiv-mul-Ω-mapping = right-equiv-mul-Ω-mapping

  Ω-mapping-Wild-Group : Wild-Group (l1 ⊔ l2)
  pr1 Ω-mapping-Wild-Group = Ω-mapping-Wild-Monoid
  pr2 Ω-mapping-Wild-Group = is-binary-equiv-mul-Ω-mapping
```
