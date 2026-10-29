module
public import Mathlib
public import BDS.Defs
public import BDS.TwoTransitiveIrreducible
public import BDS.AdditiveRelations
public import BDS.RootsCorollaries
public import BDS.AtomBridge

@[expose] public section
/-!
# The additive theorem for 2-transitive Galois groups (Girstmair; Dixon, Theorem 1′) and its engine

Index of the library. The compared statements are in `Challenge.lean`; `Solution.lean` proves each
of them by one application of the theorem of the same name in namespace `BDS`. The library name
`BDS` is historical; the multiplicative Baron–Drmota–Skałba theorem is not formalized. Throughout,
`K` is a field (of characteristic 0 where the engine is used).

* `BDS.Defs` — the definitions the compared statements use (`zeroSum`, `relModule`); the same text
  as the shared block of `Challenge.lean`, so that the Challenge imports Mathlib only.
* `BDS.TwoTransitiveIrreducible` — the engine (classical; Dixon p. 297, citing Curtis–Reiner §32B):
  `zeroSum_irreducible`, the irreducibility of the augmentation `K[G]`-module of a finite
  2-transitive action, `K` of characteristic 0.
* `BDS.AdditiveRelations` — the additive theorem (Girstmair 1982, Proposition 4, Assertion 3;
  Dixon, Theorem 1′), homogeneous case with coefficients in `K`: the criterion forms (the 'if'
  direction of Girstmair 1982, Proposition 4, Assertion 2) `additive_core_of_irreducible` and
  `relModule_le_span_one_of_irreducible` (any field, hypothesis: `V₀` irreducible, and, for the
  second, a transitive action), and the 2-transitive forms `additive_core` (the abstract core),
  `relModule_le_span_one` (every relation is a multiple of the all-ones tuple) and
  `additive_roots_no_relation` (the roots of an irreducible `f : K[X]` with 2-transitive Galois
  group satisfy no nontrivial zero-sum `K`-linear relation).
* `BDS.RootsCorollaries` — the additive theorem at the roots of an irreducible `f : K[X]` with
  2-transitive Galois group, compared statements (5) and (6): `relModule_roots_le_span_one`
  (compared statement (4) instantiated at the roots) and `roots_inhomogeneous_iff_const` (a
  relation has value in `K` if and only if its coefficients are constant; Dixon's printed form
  `U = K·e`), with its two directions `roots_inhomogeneous_const` and
  `exists_sum_rootSet_eq_algebraMap` (the sum of the roots of a separable polynomial lies in `K`).
* `BDS.AtomBridge` — uncompared: the hypothesis `hirr` of the criterion forms is atomicity of `V₀`
  in Mathlib's lattice `Subrepresentation` of the permutation representation on `Ω → K`
  (`isAtom_zeroSumSubrep_iff`), and the engine in that form (`isAtom_zeroSumSubrep`).
-/
