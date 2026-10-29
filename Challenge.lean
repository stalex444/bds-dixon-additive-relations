module
public import Mathlib

@[expose] public section
/-!
# The additive theorem for 2-transitive Galois groups (Girstmair; Dixon, Theorem 1′) and its engine

Eight compared statements, (1), (2′), (2), (3), (4′), (4), (5) and (6) below. Throughout, `K` is a
field: of characteristic 0 in (1), (2), (3), (4), (5) and (6); arbitrary in (2′) and (4′).

The engine (1): for a finite group `G` acting 2-transitively on a finite set `Ω` with `2 ≤ |Ω|`,
and a field `K` of characteristic 0, the augmentation (zero-sum) subspace
`V₀ = {f : Ω → K | ∑ x, f x = 0}` of the permutation module `Ω → K` is an irreducible
`K[G]`-module. This is classical (Huppert, *Endliche Gruppen I*, p. 597, Satz 20.2, as cited by
Girstmair 1999, p. 78). Dixon, *Acta Arith.* 82 (1997) 293–302, uses it on p. 297, in the proof of
Theorem 1(ii), citing Curtis–Reiner §32B.

On the engine rests the additive theorem for 2-transitive Galois groups. Girstmair states it in
*Manuscripta Math.* 39 (1982) 81–97, Proposition 4, Assertion 3 (p. 86): "If G is doubly
transitive on G/H, (G,H) admits only trivial relations", for every field `K` whose characteristic
does not divide `|G|`. Dixon states it as Theorem 1′ (p. 301), for a subfield `K` of `ℂ` and
relations with value in `K`. Compared statements (2), (3), (4), (5) and (6) concern it with
coefficients in a field `K` of characteristic 0; (2), (3), (4) and (5) its homogeneous case
(relations `∑ c_α α = 0`), and (6) Dixon's printed form (relations with value in `K`):
* (2) the zero-sum form, for an abstract family: no nontrivial relation with `∑ c_α = 0`;
* (3) the zero-sum form at the roots: if `f ∈ K[X]` is irreducible of degree `≥ 2` and its Galois
  group acts 2-transitively on the roots of `f` in the splitting field, then the roots satisfy no
  nontrivial `K`-linear relation with value 0 and coefficient sum 0;
* (4) the span-one form, for an abstract family: every coefficient tuple `c` with
  `∑ x, c x • α x = 0` is a scalar multiple of the all-ones tuple;
* (5) the span-one form at the roots: under the hypotheses of (3), every coefficient tuple `c` with
  `∑ r, c r • r = 0` is a scalar multiple of the all-ones tuple;
* (6) the printed form at the roots: under the hypotheses of (3), `∑ r, c r • r` lies in `K` if
  and only if `c` is constant.

So at the roots, over every field of characteristic 0, (3) is the zero-sum part of the homogeneous
case of Dixon's Theorem 1′, (5) the homogeneous case and (6) the printed form.

**The criterion forms (2′) and (4′).** The proofs of (2) and (4) use 2-transitivity only through
the irreducibility of `V₀`, and (4) also through transitivity. (2′) and (4′) take that
irreducibility as a hypothesis, `hirr`, whose text is word for word the conclusion of (1):
`∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω → (G-invariance of W) → W ≠ ⊥ → W = zeroSum K Ω`.
(`hirr` also holds, vacuously, when `V₀ = 0`, that is `|Ω| ≤ 1`, where both conclusions are
trivial.) They hold over every field `K` and for every group `G`, finite or not. (2) is (1)
followed by (2′), and (4) is (1) followed by (4′).
* (2′) the zero-sum form under `hirr`: no nontrivial zero-sum `K`-linear relation. No transitivity
  is assumed.
* (4′) the span-one form under `hirr` and transitivity. This is the 'if' direction of Girstmair
  1982, Proposition 4, Assertion 2 (p. 86): "If G is primitive on G/H, (G,H) admits only trivial
  relations over K iff the complementary module U(G/H) of Kε̄₀ is simple". Girstmair's hypothesis
  is, like `hirr`, the simplicity of a module. Girstmair 1999 restates the criterion in character
  form as Proposition 12 (p. 78), which he introduces as "essentially contained in Proposition 4
  of [11]", [11] being the 1982 paper.
* Girstmair assumes primitivity; (4′) assumes transitivity. For a transitive action, `hirr`
  already forces primitivity (elementary, not formalized: the zero-sum functions constant on the
  blocks of a nontrivial block system form a nonzero proper `G`-invariant subspace of `V₀`), so
  the difference is one of form only.
* Girstmair assumes a finite `G` and `char K ∤ |G|`. (2′) and (4′) take any field and any group,
  but their content is carried by `hirr`, which this entry proves only in characteristic 0 and
  only for 2-transitive actions, as (1). Characteristic 0, assumed in (1), (2), (3), (4), (5) and
  (6), is a sub-case of Girstmair's hypothesis. In place of the Galois conjugates of a root, (2′)
  and (4′) take an injective family with compatible linear maps.

**Setting.** The permutation module is the space of functions `Ω → K`. Mathlib's
`Representation.ofMulAction K G Ω` acts instead on `K[Ω] = MonoidAlgebra K Ω`. That carrier is
related to `Ω →₀ K` by `MonoidAlgebra.coeffLinearEquiv`, and `Ω →₀ K` to `Ω → K` by
`Finsupp.equivFunOnFinite` (`Ω` is finite). The action formula is
`Representation.coeff_ofMulAction`, which is the permutation representation
`(g • f) x = f (g⁻¹ • x)` used here.
- A `G`-subrepresentation is modeled as a `Submodule K (Ω → K)` `W` together with an explicit
  invariance hypothesis `∀ g f, f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W`. This needs no bundled
  `Rep`/`asModule` machinery. The invariance hypothesis is the defining condition of a
  subrepresentation of the permutation representation on `Ω → K` (`BDS.permRep`, in the
  uncompared bridge); its transport to `ofMulAction` on `K[Ω]` is not formalized.
- `zeroSum K Ω` is `V₀`. `relModule K α` is the `K`-submodule of coefficient tuples `c : Ω → K`
  with `∑ x, c x • α x = 0`.
- In (2), (2′), (4) and (4′), `φ` is any family of `K`-linear maps `L →ₗ[K] L` with
  `φ g (α x) = α (g • x)`. No homomorphism property is assumed.
- In the concrete statements (3), (5) and (6), the group is `f.Gal` and the set is
  `f.rootSet f.SplittingField`, acted on by Mathlib's instance `Polynomial.Gal.galActionAux`. The
  family `α` is the inclusion of the root set into the splitting field (`Subtype.val`, written
  `fun r => (r : f.SplittingField)` in (5)), and `φ g` is the field automorphism `g` read as a
  `K`-linear map. The compatibility `φ g (α x) = α (g • x)` therefore holds by `rfl`.
- In (6), a value `k : K` is read in the splitting field through `algebraMap K f.SplittingField`.

**Scope.** This entry formalizes the ADDITIVE theorem only.
- The engine's "irreducible" is proved in the substantive form of simplicity: a `G`-invariant
  subspace `W ≤ V₀` with `W ≠ ⊥` equals `V₀`.
- (1) holds over every field `K` of characteristic 0, so in particular over an algebraically closed
  one (`ℂ`, or an algebraic closure of `ℚ`). There it says that no `K`-subspace of `V₀ ⊆ Ω → K`
  other than `0` and `V₀` is `G`-invariant. This is Dixon's "indeed, absolutely irreducible",
  stated for `K`-subspaces of `Ω → K`; the identification of `Ω → K` with the scalar extension of
  `Ω → ℚ` is not formalized.
- 2-transitivity is a HYPOTHESIS: `IsMultiplyPretransitive G Ω 2` in (1), (2) and (4), and
  `IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2` in (3), (5) and (6). That a
  particular Galois group is 2-transitive is not proved here.
- In (2′) and (4′) the hypothesis is `hirr` (with transitivity, `IsPretransitive G Ω`, in (4′)).
  This entry proves `hirr` only in the 2-transitive case, as (1).
- In (3), (5) and (6), the splitting field `f.SplittingField` appears in the 2-transitivity
  hypothesis and in the statement: in the types of `c` and `hcα` in (3), in the root family of
  (5), and in the type of `c` and the left-hand side of the equivalence in (6).

**Fidelity to Dixon's Theorem 1′.** Dixon states Theorem 1′ for any subfield `K` of `ℂ`, and for
relations whose value lies in `K` (`∑ c_α α ∈ K`, coefficients in `K`). Compared statements (2),
(3), (4), (5) and (6) take any field `K` of characteristic 0 (every subfield of `ℂ` is one), with
value `0` in (2), (3), (4) and (5) and value in `K` in (6); (2′) and (4′) take any field.
- (3) is the zero-sum case of Theorem 1′ at the roots: value 0 and coefficient sum 0. The
  homogeneous case at the roots (every relation with value 0 is a multiple of the all-ones tuple)
  is (5), which is (4) instantiated at the roots.
- Dixon's printed form (value in `K`) at the roots, for every field `K` of characteristic 0, is
  (6): Dixon's module `U` of coefficient tuples `c` with `∑ c_α α ∈ K` equals `K·e`, `e` the
  all-ones tuple. Both inclusions are proved: `U ⊆ K·e` is the substance of the theorem, and
  `K·e ⊆ U`, which Dixon notes always holds, is the fact that the sum of the roots lies in `K`.
- Dixon's roots lie in `ℂ`; here they lie in Mathlib's abstract `f.SplittingField`, and no
  embedding into `ℂ` is formalized.
- The hypothesis `2 ≤ f.natDegree` of (3), (5) and (6) is not in Dixon's Theorem 1′. It excludes
  only `deg f ≤ 1`, where the root set has at most one element, and where the conclusions of (3),
  (5) and (6) hold trivially (a zero-sum tuple on at most one point is `0`, every tuple on at most
  one point is constant, and the root of a polynomial of degree 1 lies in `K`).

**The compared statements** (namespace `DixonRelations`), in the order of `comparator.json`.
- (1) `zeroSum_irreducible` — for a finite group `G` acting 2-transitively on a finite `Ω` with
  `2 ≤ |Ω|`, and a field `K` of characteristic 0: any `G`-invariant `K`-subspace `W` of `Ω → K`
  with `W ≤ V₀` and `W ≠ ⊥` is all of `V₀` (the substantive half of simplicity of the
  augmentation `K[G]`-module `V₀`).
- (2′) `additive_core_of_irreducible` — for any field `K`, any group `G` acting on a finite `Ω`, an
  injective family `α : Ω → L` into a `K`-vector space `L`, `K`-linear maps `φ g` with
  `φ g (α x) = α (g • x)`, and the hypothesis `hirr`: any `c` with `∑ x, c x = 0` and
  `∑ x, c x • α x = 0` is `0`.
- (2) `additive_core` — for an injective family `α : Ω → L` into a `K`-vector space `L` (`K` of
  characteristic 0), a 2-transitive action of a finite group `G` on a finite `Ω` with `2 ≤ |Ω|`,
  and `K`-linear maps `φ g` with `φ g (α x) = α (g • x)`: the only zero-sum `K`-linear relation
  among the `α x` is trivial. That is, any `c` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`.
- (3) `additive_roots_no_relation` — for `f ∈ K[X]` (`K` of characteristic 0) irreducible of
  degree `≥ 2` whose Galois group acts 2-transitively on the roots in the splitting field: any
  `c : f.rootSet f.SplittingField → K` with `∑ r, c r = 0` and
  `∑ r, c r • (r : f.SplittingField) = 0` is `0`. This is the zero-sum part (`U₁ ∩ V₀ = 0`) of the
  homogeneous case of Dixon's Theorem 1′, where Dixon's `U₁` is the module of coefficient tuples
  of relations with value 0. The full homogeneous case at the roots, `U₁ ⊆ K·e` with `e` the
  all-ones tuple, is (5); the inhomogeneous case (`∑ c_r r ∈ K`) is (6).
- (4′) `relModule_le_span_one_of_irreducible` — under the hypotheses of (2′), if `G` acts
  transitively on `Ω`: `relModule K α` is contained in the line spanned by the constant tuple `1`.
- (4) `relModule_le_span_one` — under the hypotheses of (2), `relModule K α` is contained in the
  line spanned by the constant tuple `1`: every `K`-linear relation among the `α x` is a scalar
  multiple of the all-ones tuple.
  - The all-ones tuple is itself a relation exactly when `∑ x, α x = 0`. Otherwise (4) and (4′)
    say there is no nonzero relation.
  - (4) is stated for an abstract family `α`. At the roots it applies by the instantiation used
    for (3), which is (5).
- (5) `relModule_roots_le_span_one` — under the hypotheses of (3): `relModule K` of the root family
  `fun r => (r : f.SplittingField)` is contained in the line spanned by the constant tuple `1`.
  That is, every `K`-linear relation among the roots with value 0 is a scalar multiple of the
  all-ones tuple (Dixon's `U₁ ⊆ K·e`).
- (6) `roots_inhomogeneous_iff_const` — under the hypotheses of (3): for
  `c : f.rootSet f.SplittingField → K`, there is `k : K` with
  `∑ r, c r • (r : f.SplittingField) = algebraMap K f.SplittingField k` if and only if there is
  `t : K` with `c = fun _ => t` (Dixon's `U = K·e`).

**Attributions.**
- K. Girstmair, "Linear dependence of zeros of polynomials and construction of primitive
  elements", *Manuscripta Math.* 39 (1982) 81–97. Proposition 4 (p. 86) concerns finite groups
  `G ⊇ H` and "K a field with char(K) prime to |G|". Assertion 1: an imprimitive pair admits
  non-trivial relations. Assertion 2: the criterion quoted above. Assertion 3: a doubly transitive
  pair admits only trivial relations, which "follows from 2. and character theory (see e.g. [2],
  p. 597)", [2] being Huppert's book. Proposition 1 (p. 83) identifies the relation modules of a
  root with the submodules of `K(G/H)` "belonging to H". (4′) formalizes the 'if' direction of
  Assertion 2, and (2′) its part on zero-sum relations; (2), (3), (4) and (5) formalize the
  characteristic-0 case of Assertion 3, (2) and (3) in zero-sum form, (3) and (5) at the roots.
- K. Girstmair, "Linear relations between roots of polynomials", *Acta Arith.* 89 (1999) 53–96,
  p. 78. Proposition 12 restates the criterion in character form: "An imprimitive pair (G,H) is
  never K-trivial." and "A primitive pair (G,H) is K-trivial if, and only if, the character
  ψ = 1_H^G − 1 is K-irreducible". The same page states that a doubly transitive pair is
  K-trivial (no additive relation except a multiple of `x₁ + … + xₙ`) for every field of
  characteristic 0, and records that this "was observed in [11] (for the additive case, to be
  precise) and by later authors", citing Baron–Drmota–Skałba 1995, Theorem 3, and Dixon 1997,
  Theorem 1 (Dixon's multiplicative theorem).
- Girstmair's Propositions 13–14 (1999) give `ℚ`-trivial pairs that are not doubly transitive:
  Proposition 13 characterizes the `ℚ`-trivial pairs among the transitive subgroups of
  `AGL(1,q)` (not doubly transitive when their index `d` exceeds 1), and Proposition 14 gives
  certain `PSL(2,q)`. (2′) and (4′) apply to such a pair over `ℚ` once `hirr` is supplied over
  `ℚ`; no such case is proved here.
- J. D. Dixon, "Polynomials with nontrivial relations between their roots", *Acta Arith.* 82
  (1997) 293–302, states the additive theorem as Theorem 1′ (p. 301), the statement this entry
  formalizes in the case described above. Dixon omits its proof ("The proofs are very similar and
  are omitted").
- The engine is classical: Huppert, *Endliche Gruppen I* (Springer 1967), p. 597, Satz 20.2, as
  cited by Girstmair 1999 (p. 78; Girstmair 1982, p. 86, cites the same page). Dixon (p. 297)
  cites C. W. Curtis & I. Reiner, *Representation Theory of Finite Groups and Associative
  Algebras* (Wiley 1962), §32B, for it.
- Girstmair 1982 was read in part (pp. 81, 83, 86 and 97). Huppert and Curtis–Reiner were not
  opened for this entry.
- Background:
  - M. Drmota & M. Skałba, "On multiplicative and linear independence of polynomial roots",
    *Contributions to General Algebra* 7 (1991) 127–135. Girstmair 1999 (p. 53) writes that "some
    minor observations of [11] appear as main results in later articles (cf., e.g., [11],
    Proposition 4, Assertion 3 and [9], Theorem 3)", [9] being this paper. Not opened.
  - C. J. Smyth, "Additive and multiplicative relations connecting conjugate algebraic numbers",
    *J. Number Theory* 23 (1986) 243–254. Dixon (p. 293) describes its Lemma 1 as showing "that
    the existence of a nontrivial relation between the roots implies that G does not act as the
    symmetric group on Ω (see Theorem 1 below for a significant generalization)". Not opened.
  - G. Baron, M. Drmota & M. Skałba, "Polynomial relations between polynomial roots", *J. Algebra*
    177 (1995) 827–846. Its Theorem 3 is on the multiplicative side (per Zheng 2021,
    arXiv:1912.07202v1, p. 2), NOT formalized here; see **Not formalized**. Not opened.
  - T. Zheng, "A fast algorithm for computing multiplicative relations between the roots of a
    generic polynomial", *J. Symbolic Comput.* 104 (2021) 381–401 (preprint arXiv:1912.07202,
    "Computing Multiplicative Relations between Roots of a Polynomial"). This is the multiplicative
    side.

**Prior formalizations.** These come from a search of 2026-10-28 for the six statements (1), (2′),
(2), (3), (4′) and (4) as stated here (over a field `K`), at the repository heads listed in
`README.md`. It is a search result, not a guarantee. (5) and (6) were searched for on 2026-10-29,
at the repository heads listed in `README.md`, and were not found.
- None of the six statements searched was found in any prover.
- The `Sₙ` case of (1) is formalized in augmentation form over every field in which `|Ω| ≠ 0`
  (every field when `|Ω| = 2`), in particular over `ℚ`, in TauCeti
  (`TauCeti.isIrreducible_standardRepresentation`, since 2026-08-05), and as Specht-module
  irreducibility over `ℂ` in openai/math.
- The general 2-transitive case of (1) is formalized in character form over `ℂ` in AxiomMath/CFSG
  (`CFSG.permutation_character_orbit_count`, public since 2026-10-27). CFSG also defines the same
  `V₀` over `ℂ`, under the same action (`CFSG.Wreathed.CentralSL2.sumZeroSubrep`), and computes
  its character, from which the `ℂ` case of (1) in submodule form would follow in a few lines; no
  theorem stating it was found.
- Nothing is imported from any of these libraries.

**The proofs.** (1) is proved by an elementary, character-free stabilizer-averaging argument. Dixon
(p. 297) cites Curtis–Reiner §32B for the statement only; Curtis–Reiner was not consulted, and
nothing is claimed about its proof.
- Proof of (1). Average a nonzero `w ∈ W` over the stabilizer of a point `a` (characteristic 0
  makes the average defined). 2-transitivity makes the average two-valued: the value `w a` at `a`,
  and a single constant off `a`. It is genuinely two-valued, since otherwise the nonzero average
  would be a constant with zero sum. So each standard difference `e_b − e_a` lies in `W`. These
  span `V₀`, so `W = V₀`.
- Proof of (2′). Apply `hirr` to `W = relModule K α ⊓ zeroSum K Ω`, which is `G`-invariant. If
  `W = ⊥`, the conclusion is immediate. If `W ≠ ⊥`, then `W = V₀` by `hirr`, and `W` has a nonzero
  zero-sum vector, so `Ω` has two distinct points `a ≠ b`, and `e_a − e_b ∈ relModule K α` forces
  `α a = α b`, contradicting injectivity.
- Proof of (4′). For a relation `c` and `g ∈ G`, applying `φ g` shows that the translate
  `x ↦ c (g⁻¹ • x)` is again a relation, with the same coefficient sum. So their difference is a
  zero-sum relation, hence `0` by (2′). Thus `c` is `G`-invariant, hence constant by transitivity.
  No averaging is used.
- Proof of (2) and (4). (2′) and (4′), with `hirr` supplied by (1) and, for (4), transitivity by
  2-transitivity.
- Proof of (3). Instantiate (2) at `G = f.Gal`, `Ω = f.rootSet f.SplittingField`, `α = Subtype.val`
  (injective), and `φ g` the field automorphism `g` as a `K`-linear map (compatibility `rfl`). The
  bound `|Ω| = deg f ≥ 2` comes from `card_rootSet_eq_natDegree`, with separability from
  `Irreducible.separable` (characteristic 0) and splitting from the splitting field.
- Proof of (5). Instantiate (4) in the same way.
- Proof of (6), forward direction. Each Galois translate of `c` has the same value `k` and the
  same coefficient sum, so the difference is a zero-sum relation among the roots, hence `0` by
  (2). So `c` is Galois-invariant, hence constant, since the Galois group acts transitively on the
  roots. This reduction step uses no averaging; the averaging is in the proof of (1), on which (2)
  rests.
- Proof of (6), reverse direction. The splitting field of the separable polynomial `f` is Galois
  over `K` (`IsGalois.of_separable_splitting_field`), and every automorphism permutes the roots, so
  it fixes their sum; a Galois-fixed element lies in `K`
  (`IsGalois.mem_range_algebraMap_iff_fixed`). So `∑ r, t • r = t • ∑ r, r` lies in `K`. This
  step needs only that `f` is separable (`BDS.exists_sum_rootSet_eq_algebraMap`).

**Not formalized.** The MULTIPLICATIVE theorem is NOT formalized and is NOT claimed. This is
Dixon's Theorem 1(ii) and, per Zheng 2021 (arXiv:1912.07202v1, p. 2), Theorem 3 of
Baron–Drmota–Skałba 1995 (not opened).
- It concerns multiplicative relations `∏ αᵢ^{mᵢ} ∈ K` among the roots, where 2-transitivity does
  NOT force triviality. For example, for a prime `p` and `b ∈ ℚ` not a `p`-th power, `Xᵖ − b` has
  Galois group `AGL(1,p)` over `ℚ`, acting sharply 2-transitively on the roots, and the ratios of
  its roots are `p`-th roots of unity: nontrivial multiplicative relations.
- Dixon's Theorem 1(ii) gives necessary conditions for that exception: `deg f = p` prime, `G`
  isomorphic to the affine group of order `p(p − 1)`, and, if `K ⊆ ℝ` and `deg f > 2`,
  `f = Xᵖ − b`. None of this multiplicative content is proved or claimed here.
- The additive theorem, (2), (3), (4), (5) and (6), carries no such exception, because the
  additive module cannot contain any `e_γ − e_δ` (Dixon, p. 301). That is why it, and not the
  multiplicative theorem, is what this entry formalizes.
- Also not formalized:
  - the 2-transitivity of any particular Galois group (it is a hypothesis in (1), (2), (3), (4),
    (5) and (6), not a theorem of this entry);
  - any case of `hirr` other than the 2-transitive one, (1);
  - the imprimitive case (Girstmair 1982, Proposition 4, Assertion 1; Girstmair 1999,
    Proposition 12, first sentence), and the fact, stated above, that `hirr` forces primitivity
    for a transitive action;
  - the 'only if' direction of the criterion (Girstmair 1982, Proposition 4, Assertion 2;
    Girstmair 1999, Proposition 12), the character form of its hypothesis, and the converse of
    Assertion 3 that Girstmair 1982 states for a splitting field;
  - the identification of `Ω → K`, for `K` an extension of `ℚ`, with the scalar extension of
    `Ω → ℚ`.

**Definitions.** The entry's definitions `zeroSum` and `relModule` are stated in this file, between
the lines `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`. That text is byte for byte
the body of `BDS/Defs.lean`, on which the proof modules are built. This file imports Mathlib only.
The namespace `BDS` of the two definitions is the development's historical name (after
Baron–Drmota–Skałba). The results formalized here are the additive ones of Girstmair and Dixon; no
result of Baron–Drmota–Skałba is formalized.
-/

-- BEGIN SHARED DEFINITIONS
-- The definitions of this entry that the compared statements use. This block is, byte for byte,
-- the body of `BDS/Defs.lean`, on which the proof modules are built; both files import Mathlib
-- only.

namespace BDS

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The augmentation (zero-sum) subspace `{f : Ω → K | ∑ x, f x = 0}` of the permutation
module `Ω → K` over a field `K`. -/
def zeroSum (K : Type*) [Field K] (Ω : Type*) [Fintype Ω] : Submodule K (Ω → K) where
  carrier := {f | ∑ x, f x = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, Pi.zero_apply, Finset.sum_const_zero]
  smul_mem' := fun c f hf => by
    simp only [Set.mem_setOf_eq] at hf ⊢
    have : ∑ x, (c • f) x = c * ∑ x, f x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by simp only [Pi.smul_apply, smul_eq_mul])
    rw [this, hf, mul_zero]

section Additive

variable (K : Type*) [Field K] {L : Type*} [AddCommGroup L] [Module K L]

/-- The `K`-submodule of coefficient tuples `c : Ω → K` giving a vanishing `K`-linear
combination `∑ x, c x • α x = 0` of the family `α` in the `K`-vector space `L`. The field `K` is
an explicit argument, since `α` does not determine it. -/
def relModule (α : Ω → L) : Submodule K (Ω → K) where
  carrier := {c | ∑ x, c x • α x = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ∑ x, (a + b) x • α x = (∑ x, a x • α x) + (∑ x, b x • α x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by rw [Pi.add_apply, add_smul])
    rw [this, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  smul_mem' := fun r c hc => by
    simp only [Set.mem_setOf_eq] at hc ⊢
    have : ∑ x, (r • c) x • α x = r • ∑ x, c x • α x := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_assoc])
    rw [this, hc, smul_zero]

end Additive

end BDS
-- END SHARED DEFINITIONS

open MulAction
open scoped BigOperators

open BDS

namespace DixonRelations

/-- **(1) Irreducibility of the augmentation module of a 2-transitive action** (classical; Dixon
p. 297, citing Curtis–Reiner §32B). Let a finite group `G` act 2-transitively on a finite set `Ω`
with `2 ≤ |Ω|`, and let `K` be a field of characteristic 0. Then any `G`-invariant `K`-subspace `W`
of the permutation module `Ω → K` that lies inside the zero-sum subspace `V₀` and is nonzero is all
of `V₀`. Together with the elementary facts, not part of this statement, that `V₀` is `G`-invariant
and nonzero when `2 ≤ |Ω|`, this is simplicity of the `K[G]`-module `V₀`. -/
theorem zeroSum_irreducible
    {K : Type*} [Field K] [CharZero K]
    {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    (h2 : IsMultiplyPretransitive G Ω 2)
    (hcard : 2 ≤ Fintype.card Ω)
    (W : Submodule K (Ω → K))
    (hWV : W ≤ zeroSum K Ω)
    (hWinv : ∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W)
    (hWne : W ≠ ⊥) :
    W = zeroSum K Ω := by
  sorry

/-- **(2′) The additive theorem under the irreducibility criterion, zero-sum form.** Let a group
`G` (not necessarily finite) act on a finite set `Ω`, let `K` be any field, let `α : Ω → L` be an
injective family in a `K`-vector space `L`, and let `φ g : L →ₗ[K] L` (one for each `g`; no
homomorphism property is assumed) satisfy `φ g (α x) = α (g • x)`. Suppose `hirr`: every nonzero
`G`-invariant `K`-subspace of the zero-sum subspace `V₀` is all of `V₀` (the conclusion of (1),
word for word). Then the family `α` admits no nontrivial zero-sum `K`-linear relation: any
`c : Ω → K` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`. No transitivity is assumed. -/
theorem additive_core_of_irreducible
    {K : Type*} [Field K]
    {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    {L : Type*} [AddCommGroup L] [Module K L]
    (α : Ω → L) (hα : Function.Injective α)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    (hirr : ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
      (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ → W = zeroSum K Ω)
    {c : Ω → K} (hc0 : ∑ x, c x = 0) (hcα : ∑ x, c x • α x = 0) :
    c = 0 := by
  sorry

/-- **(2) Abstract additive theorem, zero-sum form** (Dixon, Theorem 1′, homogeneous case,
zero-sum part, for an abstract family; over a field `K` of characteristic 0).
Let a finite group `G` act 2-transitively on a finite set `Ω` with `2 ≤ |Ω|`, let `K` be a field of
characteristic 0, let `α : Ω → L` be an injective family in a `K`-vector space `L`, and let
`φ g : L →ₗ[K] L` (one for each `g`; no homomorphism property is assumed) satisfy
`φ g (α x) = α (g • x)`. Then the family `α` admits no nontrivial zero-sum `K`-linear relation:
any `c : Ω → K` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`. -/
theorem additive_core
    {K : Type*} [Field K] [CharZero K]
    {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {L : Type*} [AddCommGroup L] [Module K L]
    (α : Ω → L) (hα : Function.Injective α)
    (hcard : 2 ≤ Fintype.card Ω)
    (h2 : IsMultiplyPretransitive G Ω 2)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    {c : Ω → K} (hc0 : ∑ x, c x = 0) (hcα : ∑ x, c x • α x = 0) :
    c = 0 := by
  sorry

open Polynomial in
/-- **(3) The additive theorem at the roots of an irreducible polynomial, zero-sum form** (Dixon,
Theorem 1′, homogeneous case, zero-sum part; over a field `K` of characteristic 0).
Let `f : K[X]` be irreducible of degree `≥ 2` and suppose its Galois group acts 2-transitively on
the roots of `f` in the splitting field. Then the roots satisfy no nontrivial zero-sum `K`-linear
relation: any `c : f.rootSet f.SplittingField → K` with `∑ r, c r = 0` and
`∑ r, c r • (r : f.SplittingField) = 0` is identically `0`. -/
theorem additive_roots_no_relation
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2)
    {c : f.rootSet f.SplittingField → K}
    (hc0 : ∑ r, c r = 0)
    (hcα : ∑ r, c r • (r : f.SplittingField) = 0) :
    c = 0 := by
  sorry

/-- **(4′) The additive theorem under the irreducibility criterion, span-one form** (the 'if'
direction of Girstmair 1982, Proposition 4, Assertion 2, p. 86, in its module form; restated in
character form as Girstmair 1999, Proposition 12, p. 78; with transitivity, which under `hirr`
forces primitivity; see the module docstring). Under the hypotheses of
`additive_core_of_irreducible` (any field `K`, any group `G`, the hypothesis `hirr`), if moreover
`G` acts transitively on `Ω`, then every `K`-linear relation among the family `α` is a scalar
multiple of the all-ones tuple: `relModule K α` is contained in the line spanned by the constant
tuple `1`. -/
theorem relModule_le_span_one_of_irreducible
    {K : Type*} [Field K]
    {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    {L : Type*} [AddCommGroup L] [Module K L]
    (α : Ω → L) (hα : Function.Injective α)
    (htr : IsPretransitive G Ω)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    (hirr : ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
      (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ → W = zeroSum K Ω) :
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} := by
  sorry

/-- **(4) The relation module lies in the span of the all-ones tuple.** Under the hypotheses of
`additive_core`, every `K`-linear relation among the family `α` is a scalar multiple of the
all-ones tuple: `relModule K α` is contained in the line spanned by the constant tuple `1`. -/
theorem relModule_le_span_one
    {K : Type*} [Field K] [CharZero K]
    {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {L : Type*} [AddCommGroup L] [Module K L]
    (α : Ω → L) (hα : Function.Injective α)
    (hcard : 2 ≤ Fintype.card Ω)
    (h2 : IsMultiplyPretransitive G Ω 2)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x)) :
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} := by
  sorry

open Polynomial in
/-- **(5) The additive theorem at the roots of an irreducible polynomial, span-one form** (Dixon,
Theorem 1′, homogeneous case; over a field `K` of characteristic 0).
Let `f : K[X]` be irreducible of degree `≥ 2` and suppose its Galois group acts 2-transitively on
the roots of `f` in the splitting field. Then every `K`-linear relation among the roots is a scalar
multiple of the all-ones tuple: the module `relModule K` of coefficient tuples
`c : f.rootSet f.SplittingField → K` with `∑ r, c r • (r : f.SplittingField) = 0` is contained in
the line spanned by the constant tuple `1`. This is `relModule_le_span_one` (4) at the roots. -/
theorem relModule_roots_le_span_one
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2) :
    relModule K (fun r : f.rootSet f.SplittingField => (r : f.SplittingField))
      ≤ Submodule.span K {fun _ => (1 : K)} := by
  sorry

open Polynomial in
/-- **(6) The additive theorem at the roots of an irreducible polynomial, relations with value in
`K`** (Dixon, Theorem 1′, in its printed form `U = K·e`; over a field `K` of characteristic 0).
Let `f : K[X]` be irreducible of degree `≥ 2` and suppose its Galois group acts 2-transitively on
the roots of `f` in the splitting field. Then, for a coefficient tuple
`c : f.rootSet f.SplittingField → K`, the `K`-linear combination of the roots lies in `K`, that is,
`∑ r, c r • (r : f.SplittingField) = algebraMap K f.SplittingField k` for some `k : K`, if and
only if `c` is constant. In Dixon's notation, with `U` the module of coefficient tuples of
relations with value in `K` and `e` the all-ones tuple, this is `U = K·e`. -/
theorem roots_inhomogeneous_iff_const
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2)
    (c : f.rootSet f.SplittingField → K) :
    (∃ k : K, ∑ r, c r • (r : f.SplittingField) = algebraMap K f.SplittingField k) ↔
      ∃ t : K, c = fun _ => t := by
  sorry

end DixonRelations
