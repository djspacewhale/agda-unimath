# Images of abelian group homomorphisms

```agda
module group-theory.images-of-abelian-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universal-property-image
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.subgroups-abelian-groups
open import group-theory.subsets-abelian-groups
```

</details>

## Idea

The properties of
[images of group homomorphisms](group-theory.images-of-group-homomorphisms.md)
carry over to the abelian case. We create counterparts for many of the useful
theorems from there here.

## Definitions

### The universal property of the image of an abelian group homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1) (H : Ab l2) (f : hom-Ab G H)
  (K : Subgroup-Ab l3 H)
  where

  is-image-hom-Ab : UUω
  is-image-hom-Ab =
    {l : Level} (L : Subgroup-Ab l H) →
    leq-Subgroup-Ab H K L ↔
    ((g : type-Ab G) → is-in-Subgroup-Ab H L (map-hom-Ab G H f g))
```

### The image subgroup under an abelian group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (H : Ab l2) (f : hom-Ab G H)
  where

  subset-image-hom-Ab : subset-Ab (l1 ⊔ l2) H
  subset-image-hom-Ab = subtype-im (map-hom-Ab G H f)

  is-image-subtype-subset-image-hom-Ab :
    is-image-subtype (map-hom-Ab G H f) subset-image-hom-Ab
  is-image-subtype-subset-image-hom-Ab =
    is-image-subtype-subtype-im (map-hom-Ab G H f)

  abstract
    contains-zero-image-hom-Ab :
      contains-zero-subset-Ab H subset-image-hom-Ab
    contains-zero-image-hom-Ab =
      unit-trunc-Prop (zero-Ab G , preserves-zero-hom-Ab G H f)

  abstract
    is-closed-under-addition-image-hom-Ab :
      is-closed-under-addition-subset-Ab H subset-image-hom-Ab
    is-closed-under-addition-image-hom-Ab {x} {y} K L =
      apply-twice-universal-property-trunc-Prop K L
        ( subset-image-hom-Ab (add-Ab H x y))
        ( λ where
          ( g , refl) (h , refl) →
            unit-trunc-Prop
              ( add-Ab G g h , preserves-add-hom-Ab G H f))

  abstract
    is-closed-under-negatives-image-hom-Ab :
      is-closed-under-negatives-subset-Ab H subset-image-hom-Ab
    is-closed-under-negatives-image-hom-Ab {x} K =
      apply-universal-property-trunc-Prop K
        ( subset-image-hom-Ab (neg-Ab H x))
        ( λ where
          ( g , refl) →
            unit-trunc-Prop
              ( neg-Ab G g , preserves-negatives-hom-Ab G H f))

  is-subgroup-image-hom-Ab :
    is-subgroup-Ab H subset-image-hom-Ab
  pr1 is-subgroup-image-hom-Ab =
    contains-zero-image-hom-Ab
  pr1 (pr2 is-subgroup-image-hom-Ab) =
    is-closed-under-addition-image-hom-Ab
  pr2 (pr2 is-subgroup-image-hom-Ab) =
    is-closed-under-negatives-image-hom-Ab

  image-hom-Ab : Subgroup-Ab (l1 ⊔ l2) H
  pr1 image-hom-Ab = subset-image-hom-Ab
  pr2 image-hom-Ab = is-subgroup-image-hom-Ab

  is-image-image-hom-Ab :
    is-image-hom-Ab G H f image-hom-Ab
  is-image-image-hom-Ab K =
    is-image-subtype-subset-image-hom-Ab (subset-Subgroup-Ab H K)

  contains-values-image-hom-Ab :
    (g : type-Ab G) →
    is-in-Subgroup-Ab H image-hom-Ab (map-hom-Ab G H f g)
  contains-values-image-hom-Ab =
    forward-implication
      ( is-image-image-hom-Ab image-hom-Ab)
      ( refl-leq-Subgroup-Ab H image-hom-Ab)

  leq-image-hom-Ab :
    {l : Level} (K : Subgroup-Ab l H) →
    ((g : type-Ab G) → is-in-Subgroup-Ab H K (map-hom-Ab G H f g)) →
    leq-Subgroup-Ab H image-hom-Ab K
  leq-image-hom-Ab K =
    backward-implication (is-image-image-hom-Ab K)
```

### The image of a subgroup under a group homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1) (H : Ab l2) (f : hom-Ab G H)
  (K : Subgroup-Ab l3 G)
  where

  subset-im-hom-Subgroup-Ab : subset-Ab (l1 ⊔ l2 ⊔ l3) H
  subset-im-hom-Subgroup-Ab =
    im-subtype (map-hom-Ab G H f) (subset-Subgroup-Ab G K)

  is-in-im-hom-Subgroup-Ab : type-Ab H → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-hom-Subgroup-Ab = is-in-subtype subset-im-hom-Subgroup-Ab

  contains-zero-im-hom-Subgroup-Ab :
    contains-zero-subset-Ab H subset-im-hom-Subgroup-Ab
  contains-zero-im-hom-Subgroup-Ab =
    unit-trunc-Prop (zero-ab-Subgroup-Ab G K , preserves-zero-hom-Ab G H f)

  abstract
    is-closed-under-addition-im-hom-Subgroup-Ab :
      is-closed-under-addition-subset-Ab H subset-im-hom-Subgroup-Ab
    is-closed-under-addition-im-hom-Subgroup-Ab {x} {y} u v =
      apply-twice-universal-property-trunc-Prop u v
        ( subset-im-hom-Subgroup-Ab (add-Ab H x y))
        ( λ where
          ((x' , k) , refl) ((y' , l) , refl) →
            unit-trunc-Prop
              ( ( add-ab-Subgroup-Ab G K (x' , k) (y' , l)) ,
                ( preserves-add-hom-Ab G H f)))

  abstract
    is-closed-under-negatives-im-hom-Subgroup-Ab :
      is-closed-under-negatives-subset-Ab H subset-im-hom-Subgroup-Ab
    is-closed-under-negatives-im-hom-Subgroup-Ab {x} u =
      apply-universal-property-trunc-Prop u
        ( subset-im-hom-Subgroup-Ab (neg-Ab H x))
        ( λ where
          ((x' , k) , refl) →
            unit-trunc-Prop
              ( ( neg-ab-Subgroup-Ab G K (x' , k)) ,
                ( preserves-negatives-hom-Ab G H f)))

  im-hom-Subgroup-Ab : Subgroup-Ab (l1 ⊔ l2 ⊔ l3) H
  pr1 im-hom-Subgroup-Ab =
    subset-im-hom-Subgroup-Ab
  pr1 (pr2 im-hom-Subgroup-Ab) =
    contains-zero-im-hom-Subgroup-Ab
  pr1 (pr2 (pr2 im-hom-Subgroup-Ab)) =
    is-closed-under-addition-im-hom-Subgroup-Ab
  pr2 (pr2 (pr2 im-hom-Subgroup-Ab)) =
    is-closed-under-negatives-im-hom-Subgroup-Ab
```
