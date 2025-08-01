# Foundation

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the foundation namespace

```agda
module foundation where

open import foundation.0-connected-types public
open import foundation.0-images-of-maps public
open import foundation.0-maps public
open import foundation.1-types public
open import foundation.2-types public
open import foundation.action-on-equivalences-functions public
open import foundation.action-on-equivalences-functions-out-of-subuniverses public
open import foundation.action-on-equivalences-type-families public
open import foundation.action-on-equivalences-type-families-over-subuniverses public
open import foundation.action-on-higher-identifications-functions public
open import foundation.action-on-homotopies-functions public
open import foundation.action-on-identifications-binary-dependent-functions public
open import foundation.action-on-identifications-binary-functions public
open import foundation.action-on-identifications-dependent-functions public
open import foundation.action-on-identifications-functions public
open import foundation.apartness-relations public
open import foundation.arithmetic-law-coproduct-and-sigma-decompositions public
open import foundation.arithmetic-law-product-and-pi-decompositions public
open import foundation.automorphisms public
open import foundation.axiom-of-choice public
open import foundation.axiom-of-countable-choice public
open import foundation.axiom-of-dependent-choice public
open import foundation.bands public
open import foundation.base-changes-span-diagrams public
open import foundation.bicomposition-functions public
open import foundation.binary-dependent-identifications public
open import foundation.binary-embeddings public
open import foundation.binary-equivalences public
open import foundation.binary-equivalences-unordered-pairs-of-types public
open import foundation.binary-functoriality-set-quotients public
open import foundation.binary-homotopies public
open import foundation.binary-operations-unordered-pairs-of-types public
open import foundation.binary-reflecting-maps-equivalence-relations public
open import foundation.binary-relations public
open import foundation.binary-relations-with-extensions public
open import foundation.binary-relations-with-lifts public
open import foundation.binary-transport public
open import foundation.binary-type-duality public
open import foundation.booleans public
open import foundation.cantor-schroder-bernstein-escardo public
open import foundation.cantors-theorem public
open import foundation.cartesian-morphisms-arrows public
open import foundation.cartesian-morphisms-span-diagrams public
open import foundation.cartesian-product-types public
open import foundation.cartesian-products-set-quotients public
open import foundation.category-of-families-of-sets public
open import foundation.category-of-sets public
open import foundation.choice-of-representatives-equivalence-relation public
open import foundation.coalgebras-maybe public
open import foundation.codiagonal-maps-of-types public
open import foundation.coherently-constant-maps public
open import foundation.coherently-idempotent-maps public
open import foundation.coherently-invertible-maps public
open import foundation.coinhabited-pairs-of-types public
open import foundation.commuting-cubes-of-maps public
open import foundation.commuting-hexagons-of-identifications public
open import foundation.commuting-pentagons-of-identifications public
open import foundation.commuting-prisms-of-maps public
open import foundation.commuting-squares-of-homotopies public
open import foundation.commuting-squares-of-identifications public
open import foundation.commuting-squares-of-maps public
open import foundation.commuting-tetrahedra-of-homotopies public
open import foundation.commuting-tetrahedra-of-maps public
open import foundation.commuting-triangles-of-homotopies public
open import foundation.commuting-triangles-of-identifications public
open import foundation.commuting-triangles-of-maps public
open import foundation.commuting-triangles-of-morphisms-arrows public
open import foundation.complements public
open import foundation.complements-subtypes public
open import foundation.composite-maps-in-inverse-sequential-diagrams public
open import foundation.composition-algebra public
open import foundation.composition-spans public
open import foundation.computational-identity-types public
open import foundation.cones-over-cospan-diagrams public
open import foundation.cones-over-inverse-sequential-diagrams public
open import foundation.conjunction public
open import foundation.connected-components public
open import foundation.connected-components-universes public
open import foundation.connected-maps public
open import foundation.connected-types public
open import foundation.constant-maps public
open import foundation.constant-span-diagrams public
open import foundation.constant-type-families public
open import foundation.continuations public
open import foundation.contractible-maps public
open import foundation.contractible-types public
open import foundation.copartial-elements public
open import foundation.copartial-functions public
open import foundation.coproduct-decompositions public
open import foundation.coproduct-decompositions-subuniverse public
open import foundation.coproduct-types public
open import foundation.coproducts-pullbacks public
open import foundation.coslice public
open import foundation.cospan-diagrams public
open import foundation.cospans public
open import foundation.decidable-dependent-function-types public
open import foundation.decidable-dependent-pair-types public
open import foundation.decidable-embeddings public
open import foundation.decidable-equality public
open import foundation.decidable-equivalence-relations public
open import foundation.decidable-maps public
open import foundation.decidable-propositions public
open import foundation.decidable-relations public
open import foundation.decidable-subtypes public
open import foundation.decidable-types public
open import foundation.dependent-binary-homotopies public
open import foundation.dependent-binomial-theorem public
open import foundation.dependent-epimorphisms public
open import foundation.dependent-epimorphisms-with-respect-to-truncated-types public
open import foundation.dependent-function-types public
open import foundation.dependent-homotopies public
open import foundation.dependent-identifications public
open import foundation.dependent-inverse-sequential-diagrams public
open import foundation.dependent-pair-types public
open import foundation.dependent-products-pullbacks public
open import foundation.dependent-sequences public
open import foundation.dependent-sums-pullbacks public
open import foundation.dependent-telescopes public
open import foundation.dependent-universal-property-equivalences public
open import foundation.descent-coproduct-types public
open import foundation.descent-dependent-pair-types public
open import foundation.descent-empty-types public
open import foundation.descent-equivalences public
open import foundation.diaconescus-theorem public
open import foundation.diagonal-maps-cartesian-products-of-types public
open import foundation.diagonal-maps-of-types public
open import foundation.diagonal-span-diagrams public
open import foundation.diagonals-of-maps public
open import foundation.diagonals-of-morphisms-arrows public
open import foundation.discrete-binary-relations public
open import foundation.discrete-reflexive-relations public
open import foundation.discrete-relaxed-sigma-decompositions public
open import foundation.discrete-sigma-decompositions public
open import foundation.discrete-types public
open import foundation.disjoint-subtypes public
open import foundation.disjunction public
open import foundation.double-arrows public
open import foundation.double-negation public
open import foundation.double-negation-modality public
open import foundation.double-negation-stable-equality public
open import foundation.double-negation-stable-propositions public
open import foundation.double-powersets public
open import foundation.dubuc-penon-compact-types public
open import foundation.effective-maps-equivalence-relations public
open import foundation.embeddings public
open import foundation.empty-types public
open import foundation.endomorphisms public
open import foundation.epimorphisms public
open import foundation.epimorphisms-with-respect-to-sets public
open import foundation.epimorphisms-with-respect-to-truncated-types public
open import foundation.equality-cartesian-product-types public
open import foundation.equality-coproduct-types public
open import foundation.equality-dependent-function-types public
open import foundation.equality-dependent-pair-types public
open import foundation.equality-fibers-of-maps public
open import foundation.equivalence-classes public
open import foundation.equivalence-extensionality public
open import foundation.equivalence-induction public
open import foundation.equivalence-injective-type-families public
open import foundation.equivalence-relations public
open import foundation.equivalences public
open import foundation.equivalences-arrows public
open import foundation.equivalences-cospans public
open import foundation.equivalences-double-arrows public
open import foundation.equivalences-inverse-sequential-diagrams public
open import foundation.equivalences-maybe public
open import foundation.equivalences-span-diagrams public
open import foundation.equivalences-span-diagrams-families-of-types public
open import foundation.equivalences-spans public
open import foundation.equivalences-spans-families-of-types public
open import foundation.evaluation-functions public
open import foundation.exclusive-disjunction public
open import foundation.exclusive-sum public
open import foundation.existential-quantification public
open import foundation.exponents-set-quotients public
open import foundation.extensions-types public
open import foundation.extensions-types-global-subuniverses public
open import foundation.extensions-types-subuniverses public
open import foundation.faithful-maps public
open import foundation.families-of-equivalences public
open import foundation.families-of-maps public
open import foundation.families-over-telescopes public
open import foundation.fiber-inclusions public
open import foundation.fibered-equivalences public
open import foundation.fibered-involutions public
open import foundation.fibered-maps public
open import foundation.fibers-of-maps public
open import foundation.finite-sequences-set-quotients public
open import foundation.finitely-coherent-equivalences public
open import foundation.finitely-coherently-invertible-maps public
open import foundation.fixed-points-endofunctions public
open import foundation.freely-generated-equivalence-relations public
open import foundation.full-subtypes public
open import foundation.function-extensionality public
open import foundation.function-types public
open import foundation.functional-correspondences public
open import foundation.functoriality-action-on-identifications-functions public
open import foundation.functoriality-cartesian-product-types public
open import foundation.functoriality-coproduct-types public
open import foundation.functoriality-dependent-function-types public
open import foundation.functoriality-dependent-pair-types public
open import foundation.functoriality-disjunction public
open import foundation.functoriality-fibers-of-maps public
open import foundation.functoriality-function-types public
open import foundation.functoriality-morphisms-arrows public
open import foundation.functoriality-propositional-truncation public
open import foundation.functoriality-pullbacks public
open import foundation.functoriality-sequential-limits public
open import foundation.functoriality-set-quotients public
open import foundation.functoriality-set-truncation public
open import foundation.functoriality-truncation public
open import foundation.fundamental-theorem-of-equivalence-relations public
open import foundation.fundamental-theorem-of-identity-types public
open import foundation.global-choice public
open import foundation.global-subuniverses public
open import foundation.globular-type-of-dependent-functions public
open import foundation.globular-type-of-functions public
open import foundation.higher-homotopies-morphisms-arrows public
open import foundation.hilberts-epsilon-operators public
open import foundation.homotopies public
open import foundation.homotopies-morphisms-arrows public
open import foundation.homotopies-morphisms-cospan-diagrams public
open import foundation.homotopy-algebra public
open import foundation.homotopy-induction public
open import foundation.homotopy-preorder-of-types public
open import foundation.horizontal-composition-spans-of-spans public
open import foundation.idempotent-maps public
open import foundation.identity-systems public
open import foundation.identity-truncated-types public
open import foundation.identity-types public
open import foundation.images public
open import foundation.images-subtypes public
open import foundation.implicit-function-types public
open import foundation.impredicative-encodings public
open import foundation.impredicative-universes public
open import foundation.induction-principle-propositional-truncation public
open import foundation.infinitely-coherent-equivalences public
open import foundation.infinity-connected-maps public
open import foundation.infinity-connected-types public
open import foundation.inhabited-subtypes public
open import foundation.inhabited-types public
open import foundation.injective-maps public
open import foundation.interchange-law public
open import foundation.intersections-subtypes public
open import foundation.inverse-sequential-diagrams public
open import foundation.invertible-maps public
open import foundation.involutions public
open import foundation.irrefutable-propositions public
open import foundation.isolated-elements public
open import foundation.isomorphisms-of-sets public
open import foundation.iterated-cartesian-product-types public
open import foundation.iterated-dependent-pair-types public
open import foundation.iterated-dependent-product-types public
open import foundation.iterating-automorphisms public
open import foundation.iterating-families-of-maps public
open import foundation.iterating-functions public
open import foundation.iterating-involutions public
open import foundation.kernel-span-diagrams-of-maps public
open import foundation.large-apartness-relations public
open import foundation.large-binary-relations public
open import foundation.large-dependent-pair-types public
open import foundation.large-homotopies public
open import foundation.large-identity-types public
open import foundation.large-locale-of-propositions public
open import foundation.large-locale-of-subtypes public
open import foundation.law-of-excluded-middle public
open import foundation.lawveres-fixed-point-theorem public
open import foundation.lesser-limited-principle-of-omniscience public
open import foundation.lifts-types public
open import foundation.limited-principle-of-omniscience public
open import foundation.locale-of-propositions public
open import foundation.locally-small-types public
open import foundation.logical-equivalences public
open import foundation.maps-in-global-subuniverses public
open import foundation.maps-in-subuniverses public
open import foundation.maybe public
open import foundation.mere-embeddings public
open import foundation.mere-equality public
open import foundation.mere-equivalences public
open import foundation.mere-functions public
open import foundation.mere-logical-equivalences public
open import foundation.mere-path-cosplit-maps public
open import foundation.monomorphisms public
open import foundation.morphisms-arrows public
open import foundation.morphisms-binary-relations public
open import foundation.morphisms-coalgebras-maybe public
open import foundation.morphisms-cospan-diagrams public
open import foundation.morphisms-cospans public
open import foundation.morphisms-double-arrows public
open import foundation.morphisms-inverse-sequential-diagrams public
open import foundation.morphisms-span-diagrams public
open import foundation.morphisms-spans public
open import foundation.morphisms-spans-families-of-types public
open import foundation.morphisms-twisted-arrows public
open import foundation.multisubsets public
open import foundation.multivariable-correspondences public
open import foundation.multivariable-decidable-relations public
open import foundation.multivariable-functoriality-set-quotients public
open import foundation.multivariable-homotopies public
open import foundation.multivariable-operations public
open import foundation.multivariable-relations public
open import foundation.multivariable-sections public
open import foundation.negated-equality public
open import foundation.negation public
open import foundation.noncontractible-types public
open import foundation.null-homotopic-maps public
open import foundation.operations-span-diagrams public
open import foundation.operations-spans public
open import foundation.operations-spans-families-of-types public
open import foundation.opposite-spans public
open import foundation.pairs-of-distinct-elements public
open import foundation.partial-elements public
open import foundation.partial-functions public
open import foundation.partial-sequences public
open import foundation.partitions public
open import foundation.path-algebra public
open import foundation.path-cosplit-maps public
open import foundation.path-split-maps public
open import foundation.path-split-type-families public
open import foundation.perfect-images public
open import foundation.permutations-spans-families-of-types public
open import foundation.pi-decompositions public
open import foundation.pi-decompositions-subuniverse public
open import foundation.pointed-torsorial-type-families public
open import foundation.postcomposition-dependent-functions public
open import foundation.postcomposition-functions public
open import foundation.postcomposition-pullbacks public
open import foundation.powersets public
open import foundation.precomposition-dependent-functions public
open import foundation.precomposition-functions public
open import foundation.precomposition-functions-into-subuniverses public
open import foundation.precomposition-type-families public
open import foundation.preunivalence public
open import foundation.preunivalent-type-families public
open import foundation.principle-of-omniscience public
open import foundation.product-decompositions public
open import foundation.product-decompositions-subuniverse public
open import foundation.products-binary-relations public
open import foundation.products-equivalence-relations public
open import foundation.products-of-tuples-of-types public
open import foundation.products-pullbacks public
open import foundation.products-unordered-pairs-of-types public
open import foundation.products-unordered-tuples-of-types public
open import foundation.projective-types public
open import foundation.proper-subtypes public
open import foundation.propositional-extensionality public
open import foundation.propositional-maps public
open import foundation.propositional-resizing public
open import foundation.propositional-truncations public
open import foundation.propositions public
open import foundation.pullback-cones public
open import foundation.pullbacks public
open import foundation.pullbacks-subtypes public
open import foundation.quasicoherently-idempotent-maps public
open import foundation.raising-universe-levels public
open import foundation.reflecting-maps-equivalence-relations public
open import foundation.reflexive-relations public
open import foundation.regensburg-extension-fundamental-theorem-of-identity-types public
open import foundation.relaxed-sigma-decompositions public
open import foundation.repetitions-of-values public
open import foundation.repetitions-sequences public
open import foundation.replacement public
open import foundation.retractions public
open import foundation.retracts-of-maps public
open import foundation.retracts-of-types public
open import foundation.sections public
open import foundation.separated-types-subuniverses public
open import foundation.sequences public
open import foundation.sequential-limits public
open import foundation.set-coequalizers public
open import foundation.set-presented-types public
open import foundation.set-quotients public
open import foundation.set-truncations public
open import foundation.sets public
open import foundation.shifting-sequences public
open import foundation.sigma-closed-subuniverses public
open import foundation.sigma-decomposition-subuniverse public
open import foundation.sigma-decompositions public
open import foundation.singleton-induction public
open import foundation.singleton-subtypes public
open import foundation.slice public
open import foundation.small-maps public
open import foundation.small-types public
open import foundation.small-universes public
open import foundation.sorial-type-families public
open import foundation.span-diagrams public
open import foundation.span-diagrams-families-of-types public
open import foundation.spans public
open import foundation.spans-families-of-types public
open import foundation.spans-of-spans public
open import foundation.split-idempotent-maps public
open import foundation.split-surjective-maps public
open import foundation.standard-apartness-relations public
open import foundation.standard-pullbacks public
open import foundation.standard-ternary-pullbacks public
open import foundation.strict-symmetrization-binary-relations public
open import foundation.strictly-involutive-identity-types public
open import foundation.strictly-right-unital-concatenation-identifications public
open import foundation.strong-preunivalence public
open import foundation.strongly-extensional-maps public
open import foundation.structure public
open import foundation.structure-identity-principle public
open import foundation.structured-equality-duality public
open import foundation.structured-type-duality public
open import foundation.subsequences public
open import foundation.subsingleton-induction public
open import foundation.subterminal-types public
open import foundation.subtype-duality public
open import foundation.subtype-identity-principle public
open import foundation.subtypes public
open import foundation.subuniverses public
open import foundation.surjective-maps public
open import foundation.symmetric-binary-relations public
open import foundation.symmetric-cores-binary-relations public
open import foundation.symmetric-difference public
open import foundation.symmetric-identity-types public
open import foundation.symmetric-operations public
open import foundation.telescopes public
open import foundation.terminal-spans-families-of-types public
open import foundation.tight-apartness-relations public
open import foundation.torsorial-type-families public
open import foundation.total-partial-elements public
open import foundation.total-partial-functions public
open import foundation.transfinite-cocomposition-of-maps public
open import foundation.transport-along-equivalences public
open import foundation.transport-along-higher-identifications public
open import foundation.transport-along-homotopies public
open import foundation.transport-along-identifications public
open import foundation.transport-split-type-families public
open import foundation.transposition-identifications-along-equivalences public
open import foundation.transposition-identifications-along-retractions public
open import foundation.transposition-identifications-along-sections public
open import foundation.transposition-span-diagrams public
open import foundation.trivial-relaxed-sigma-decompositions public
open import foundation.trivial-sigma-decompositions public
open import foundation.truncated-equality public
open import foundation.truncated-maps public
open import foundation.truncated-types public
open import foundation.truncation-equivalences public
open import foundation.truncation-images-of-maps public
open import foundation.truncation-levels public
open import foundation.truncation-modalities public
open import foundation.truncations public
open import foundation.tuples-of-types public
open import foundation.type-arithmetic-booleans public
open import foundation.type-arithmetic-cartesian-product-types public
open import foundation.type-arithmetic-coproduct-types public
open import foundation.type-arithmetic-dependent-function-types public
open import foundation.type-arithmetic-dependent-pair-types public
open import foundation.type-arithmetic-empty-type public
open import foundation.type-arithmetic-standard-pullbacks public
open import foundation.type-arithmetic-unit-type public
open import foundation.type-duality public
open import foundation.type-theoretic-principle-of-choice public
open import foundation.uniformly-decidable-type-families public
open import foundation.unions-subtypes public
open import foundation.uniqueness-image public
open import foundation.uniqueness-quantification public
open import foundation.uniqueness-set-quotients public
open import foundation.uniqueness-set-truncations public
open import foundation.uniqueness-truncation public
open import foundation.unit-type public
open import foundation.unital-binary-operations public
open import foundation.univalence public
open import foundation.univalence-implies-function-extensionality public
open import foundation.univalent-type-families public
open import foundation.universal-property-booleans public
open import foundation.universal-property-cartesian-product-types public
open import foundation.universal-property-contractible-types public
open import foundation.universal-property-coproduct-types public
open import foundation.universal-property-dependent-function-types public
open import foundation.universal-property-dependent-pair-types public
open import foundation.universal-property-empty-type public
open import foundation.universal-property-equivalences public
open import foundation.universal-property-family-of-fibers-of-maps public
open import foundation.universal-property-fiber-products public
open import foundation.universal-property-identity-systems public
open import foundation.universal-property-identity-types public
open import foundation.universal-property-image public
open import foundation.universal-property-maybe public
open import foundation.universal-property-propositional-truncation public
open import foundation.universal-property-propositional-truncation-into-sets public
open import foundation.universal-property-pullbacks public
open import foundation.universal-property-sequential-limits public
open import foundation.universal-property-set-quotients public
open import foundation.universal-property-set-truncation public
open import foundation.universal-property-truncation public
open import foundation.universal-property-unit-type public
open import foundation.universal-quantification public
open import foundation.universe-levels public
open import foundation.unordered-pairs public
open import foundation.unordered-pairs-of-types public
open import foundation.unordered-tuples public
open import foundation.unordered-tuples-of-types public
open import foundation.vertical-composition-spans-of-spans public
open import foundation.weak-function-extensionality public
open import foundation.weak-limited-principle-of-omniscience public
open import foundation.weakly-constant-maps public
open import foundation.whiskering-higher-homotopies-composition public
open import foundation.whiskering-homotopies-composition public
open import foundation.whiskering-homotopies-concatenation public
open import foundation.whiskering-identifications-concatenation public
open import foundation.whiskering-operations public
open import foundation.wild-category-of-types public
open import foundation.yoneda-identity-types public
```
