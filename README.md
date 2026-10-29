# The additive theorem for 2-transitive Galois groups (Girstmair; Dixon, Theorem 1′) and its representation-theoretic engine

Kernel-checked, in Lean 4 + Mathlib.

**The engine.** Let a finite group `G` act 2-transitively on a finite set `Ω` with `2 ≤ |Ω|`, and
let `K` be a field of characteristic 0. The engine is that the augmentation (zero-sum) subspace
`V₀ = {f : Ω → K | ∑ x, f x = 0}` of the permutation module `Ω → K` is an irreducible
`K[G]`-module. Dixon uses it, over `ℚ`, in the proof of Theorem 1(ii) (*Acta Arith.* 82 (1997)
293–302, p. 297): "the QG-module V0 defined above is irreducible; indeed, it is absolutely
irreducible (see [1], Sect. 32B)".

**The additive theorem.** On the engine rests the additive theorem for 2-transitive Galois groups.
Girstmair states it in 1982 (*Manuscripta Math.* 39, 81–97, Proposition 4, Assertion 3, p. 86):
"If G is doubly transitive on G/H, (G,H) admits only trivial relations", for every field `K` whose
characteristic does not divide `|G|`. Dixon states it as Theorem 1′ (p. 301), for any subfield
`K ⊆ ℂ`: if `f ∈ K[X]` is irreducible and its Galois group acts 2-transitively on the roots, then
every `c ∈ K^Ω` with `∑ c_α α ∈ K` is a multiple of the all-ones tuple. Dixon omits the proof
("The proofs are very similar and are omitted").

**What this entry proves.** For every field `K` of characteristic 0, it proves the homogeneous case
(relations `∑ c_α α = 0`) with coefficients in `K`:
- if `∑ c_α = 0` and `∑ c_α α = 0`, then `c = 0` ((2), for an abstract family; (3), at the roots);
- every `c` with `∑ c_α α = 0` is a multiple of the all-ones tuple ((4), for an abstract family;
  (5), at the roots).

It also proves two **criterion forms**, over every field `K`: the same two conclusions with
2-transitivity replaced by the irreducibility of `V₀` (a hypothesis `hirr` whose text is word for
word the conclusion of (1); `hirr` also holds, vacuously, when `V₀ = 0`, that is `|Ω| ≤ 1`, where
both conclusions are trivial) and, for the span-one form, transitivity ((2′), (4′)).
- (4′) is the 'if' direction of Girstmair 1982, Proposition 4, Assertion 2 (p. 86: "If G is
  primitive on G/H, (G,H) admits only trivial relations over K iff the complementary module U(G/H)
  of Kε̄₀ is simple"), whose irreducibility hypothesis is stated, as `hirr` is, for a module rather
  than for a character. Girstmair 1999 restates it in character form as Proposition 12 (p. 78),
  which he introduces as "essentially contained in Proposition 4 of [11]", [11] being the 1982
  paper.
- (4′) assumes transitivity instead of primitivity (under `hirr` the two coincide; see *What is
  known*), allows any field and any group, and replaces the Galois conjugates by an injective
  family with compatible linear maps.
- (2) and (4) are (1) followed by (2′) and (4′).

The substantive inclusion of Dixon's printed form (`∑ c_α α ∈ K` forces `c` constant) follows from
the homogeneous case; the other inclusion is the fact that the sum of the roots lies in `K`. At the
roots, for every field `K` of characteristic 0, the two together are compared statement (6):
`∑ c_α α ∈ K` if and only if `c` is constant, which is Dixon's `U = K·e`.

**Research context.** Additive and multiplicative relations among conjugate algebraic numbers are
studied in Girstmair (1982, 1999), Smyth (1986), Drmota–Skałba (1991), Baron–Drmota–Skałba (1995),
Dixon (1997) and Zheng (2021). In the sources read for this entry, the doubly transitive additive
case is derived from the criterion and character theory in one sentence (Girstmair 1982, p. 86),
set aside because the doubly transitive pairs are classified (Girstmair 1999, p. 78), and stated
with its proof omitted (Dixon 1997, p. 301). This entry gives a complete, character-free,
machine-checked proof over every field of characteristic 0, all compared: the homogeneous case
(span-one form (4) for an abstract family; zero-sum form (3) and span-one form (5) at the roots),
and Dixon's printed form at the roots (6). It also proves, over every field, the 'if' direction of
Girstmair's criterion in module form.

There are eight compared theorems, each on the axioms `propext`, `Classical.choice`, `Quot.sound`
alone. This formalizes classical results; it is not new mathematics. For formalization status, see
*Prior formalizations*. The **multiplicative** theorem is deliberately **not** formalized and not
claimed (see *What is not formalized*).

## The compared statements

Namespace `DixonRelations`, in the order of `comparator.json`. The exact Lean is in
`Challenge.lean`. The two definitions it uses, `BDS.zeroSum K Ω` (`V₀`) and `BDS.relModule K α` (the
coefficient tuples `c : Ω → K` with `∑ x, c x • α x = 0`), are stated there, between
`-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`. The namespace `BDS` of the two
definitions is the development's historical name (after Baron–Drmota–Skałba). The results
formalized here are the additive ones of Girstmair and Dixon; no result of Baron–Drmota–Skałba is
formalized.

- **(1) `zeroSum_irreducible`** — the engine. For a field `K` of characteristic 0 and a finite group
  `G` acting 2-transitively on a finite `Ω` with `2 ≤ |Ω|`, any `G`-invariant `K`-subspace `W` of
  `Ω → K` with `W ≤ V₀` and `W ≠ ⊥` equals `V₀`.
  - This is the substantive half of simplicity of the `K[G]`-module `V₀`. Together with the
    elementary facts, not part of the statement, that `V₀` is `G`-invariant and nonzero, it is
    simplicity. Both facts are proved, uncompared, in the library: `BDS.zeroSum_invariant`, and the
    `V₀ ≠ ⊥` half of `BDS.isAtom_zeroSumSubrep`.
  - The `G`-action is the permutation representation `(g • f) x = f (g⁻¹ • x)`. A
    subrepresentation is a `Submodule` with an explicit invariance hypothesis, the defining
    condition of a subrepresentation of the permutation representation on `Ω → K` (`BDS.permRep`,
    in the uncompared bridge); its transport to `Representation.ofMulAction` on `K[Ω]` is not
    formalized.
  - Over an algebraically closed field `K` of characteristic 0 (`ℂ`, or an algebraic closure of
    `ℚ`), (1) says that no `K`-subspace of `V₀ ⊆ Ω → K` other than `0` and `V₀` is `G`-invariant.
    That is absolute irreducibility, stated for `K`-subspaces of `Ω → K`. The identification of
    `Ω → K` with the scalar extension of `Ω → ℚ` is not formalized.
- **(2′) `additive_core_of_irreducible`** — the zero-sum form under the irreducibility criterion.
  The data:
  - any field `K`, and any group `G`, finite or not, acting on a finite `Ω`;
  - an injective family `α : Ω → L` into a `K`-vector space `L`;
  - `K`-linear maps `φ g` with `φ g (α x) = α (g • x)` (no homomorphism property is assumed);
  - the hypothesis

    ```
    hirr : ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
      (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ → W = zeroSum K Ω
    ```

  Then any `c : Ω → K` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`. There is no
  transitivity hypothesis, no bound on `|Ω|` and no assumption on the characteristic.
- **(2) `additive_core`** — Dixon's Theorem 1′, homogeneous case, zero-sum part, for an abstract
  family. The data:
  - a field `K` of characteristic 0;
  - an injective family `α : Ω → L` into a `K`-vector space `L`;
  - a 2-transitive action of a finite group `G` on a finite `Ω` with `2 ≤ |Ω|`;
  - `K`-linear maps `φ g` with `φ g (α x) = α (g • x)` (no homomorphism property is assumed).

  Then any `c : Ω → K` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`.
- **(3) `additive_roots_no_relation`** — Dixon's Theorem 1′, homogeneous case, zero-sum part, at
  the roots. Let `K` be a field of characteristic 0 and `f ∈ K[X]` irreducible of degree `≥ 2`,
  with Galois group acting 2-transitively on the roots in the splitting field. Then any
  `c : f.rootSet f.SplittingField → K` with `∑ r, c r = 0` and
  `∑ r, c r • (r : f.SplittingField) = 0` is `0`. The splitting field `f.SplittingField` appears in
  the 2-transitivity hypothesis and in the types of `c` and `hcα`.
  - This is the zero-sum (value-0, zero-coefficient-sum) case. The general homogeneous case at the
    roots (every relation with value 0 is a multiple of the all-ones tuple) is (5), and the
    inhomogeneous case (`∑ c_r r ∈ K`) is (6).
- **(4′) `relModule_le_span_one_of_irreducible`** — the span-one form under the irreducibility
  criterion. Under the hypotheses of (2′), if `G` acts transitively on `Ω`
  (`IsPretransitive G Ω`), then `relModule K α` is contained in the line `K ∙ (fun _ => 1)`. This
  is the 'if' direction of Girstmair 1982, Proposition 4, Assertion 2, in the form described under
  *What is known*.
  - Transitivity cannot be dropped. For example (not formalized): with `|Ω| = 2`, the trivial group
    and `α = (1, 2)` in `ℚ`, `hirr` holds, since `V₀` is a line, but `(2, −1)` is a relation that
    is not a multiple of `(1, 1)`.
- **(4) `relModule_le_span_one`** — the span-one form. Under the hypotheses of (2), `relModule K α`
  is contained in the line `K ∙ (fun _ => 1)`: every coefficient tuple `c` with
  `∑ x, c x • α x = 0` is a scalar multiple of the all-ones tuple.
  - The all-ones tuple is itself a relation exactly when `∑ x, α x = 0`, as for the roots of any
    `f` whose coefficient of `X^{n−1}` is 0. Otherwise (4) and (4′) say there is no nonzero
    relation.
  - (4) is stated for an abstract family `α`. At the roots, it applies by the instantiation used
    for (3), which is (5).
- **(5) `relModule_roots_le_span_one`** — the span-one form at the roots, (4) instantiated at the
  roots. Under the hypotheses of (3), `relModule K (fun r => (r : f.SplittingField))` is contained
  in the line `K ∙ (fun _ => 1)`: every `c` with `∑ r, c r • r = 0` is a multiple of the all-ones
  tuple.
- **(6) `roots_inhomogeneous_iff_const`** — relations with value in `K`. Under the hypotheses of
  (3), `∑ r, c r • r = algebraMap K f.SplittingField k` for some `k ∈ K` if and only if `c` is
  constant. This is Dixon's Theorem 1′ (`∑ c_α α ∈ K`) for every field `K` of characteristic 0,
  with the roots in `f.SplittingField`, as the equality `U = K·e` (see *Relation to Dixon's
  statement*).
  - The proof of the forward direction (`BDS.roots_inhomogeneous_const`): each Galois translate of
    `c` has the same value `k` and the same coefficient sum, so the difference is a zero-sum
    relation, hence `0` by (2); and a Galois-invariant tuple on a transitive root set is constant.
    (Girstmair 1999, in a remark after Definition 3 on p. 62,
    reduces relations with right side in `K` to homogeneous ones by averaging when `char K ∤ |G|`;
    the reduction step here uses no averaging, and characteristic 0 enters only through (2) and the
    separability of `f`.)
  - The proof of the reverse direction: the sum of the roots lies in `K`, so `∑ r, t • r` does.
    The library lemma `BDS.exists_sum_rootSet_eq_algebraMap` proves this for every separable
    `f : K[X]` over every field `K`: the splitting field is Galois over `K`, and every automorphism
    permutes the roots, so it fixes their sum.

## Library bridge (not compared)

`BDS/AtomBridge.lean` holds a bridge from the hypothesis `hirr` to Mathlib's lattice of
subrepresentations. Neither of its two theorems is in `comparator.json` or compared; both are
kernel-checked on the same three axioms.

* `BDS.isAtom_zeroSumSubrep_iff` — `V₀` is an atom (`IsAtom`) of the lattice
  `Subrepresentation (BDS.permRep K G Ω)` if and only if `V₀ ≠ ⊥` and `hirr` holds. Here
  `BDS.permRep K G Ω` is the permutation representation on `Ω → K`, built from Mathlib's
  `LinearMap.funLeft`; its transport to `Representation.ofMulAction` on `K[Ω]` is not formalized.
* `BDS.isAtom_zeroSumSubrep` — (1) in that form: under the hypotheses of (1), `V₀` is an atom.

## What is known, what is cited, what is proved here

**Classical; no novelty of content is claimed.**
- Girstmair 1982 (*Manuscripta Math.* 39, 81–97), Proposition 4 (p. 86), for finite groups `G ⊇ H`
  and "K a field with char(K) prime to |G|":
  - Assertion 1: "If G acts imprimitively on G/H, (G,H) admits non-trivial relations over K."
  - Assertion 2: "If G is primitive on G/H, (G,H) admits only trivial relations over K iff the
    complementary module U(G/H) of Kε̄₀ is simple."
  - Assertion 3: "If G is doubly transitive on G/H, (G,H) admits only trivial relations." Its
    proof: "The third assertion follows from 2. and character theory (see e.g. [2], p. 597)", [2]
    being Huppert's book.
  - "Only trivial relations" means that `0` and `Kε̄₀` (the multiples of the all-ones tuple) are the
    only submodules of `K(G/H)` "belonging to H"; Proposition 1 (p. 83) identifies these
    submodules with the relation modules of a root.

  (4′) formalizes the 'if' direction of Assertion 2, and (2′) its part on zero-sum relations.
  (2), (3), (4) and (5) formalize the characteristic-0 case of Assertion 3, (2) and (3) in
  zero-sum form, (3) and (5) at the roots. Characteristic 0 is a sub-case of Girstmair's
  hypothesis. (2′) and (4′) take any field and any group, but their content is carried by `hirr`,
  which is proved here only in characteristic 0 and only for 2-transitive actions, as (1).
- For a transitive action, `hirr` already forces primitivity (elementary, not formalized: the
  zero-sum functions constant on the blocks of a nontrivial block system form a nonzero proper
  `G`-invariant subspace of `V₀`; compare Assertion 1). So the transitivity hypothesis of (4′)
  differs from Girstmair's primitivity in form only.
- Girstmair 1999 (*Acta Arith.* 89, 53–96) restates the criterion in character form as Proposition
  12 (p. 78), which he introduces as "essentially contained in Proposition 4 of [11]", [11] being
  the 1982 paper. Its two sentences are "An imprimitive pair (G,H) is never K-trivial." and "A
  primitive pair (G,H) is K-trivial if, and only if, the character ψ = 1_H^G − 1 is
  K-irreducible". The paragraph leading to it states the criterion in module form: "Then the pair
  (G, H) is K-trivial if, and only if, U (G) is simple as a K[G]-module" (`U(G)` being the zero-sum
  submodule of `K[G/H]`; the 1999 paper assumes `char(K) = 0` from p. 62 on). A pair is K-trivial
  when it admits no additive relation except `c·(x₁ + … + xₙ) = 0` (p. 55).
- On the same page he states that a doubly transitive pair is K-trivial for every field `K` of
  characteristic 0, and records that this "was observed in [11] (for the additive case, to be
  precise) and by later authors", citing Baron–Drmota–Skałba 1995, Theorem 3, and Dixon 1997,
  Theorem 1. Dixon's Theorem 1 is his multiplicative theorem (see *What is not formalized*);
  Dixon's additive Theorem 1′ is not among the results Girstmair cites.
- Also on p. 78 Girstmair sets the doubly transitive pairs aside: "Since there exists a complete
  classification of all doubly transitive pairs (cf., e.g., [3]), they are not of interest here."
  His Propositions 13–14 give `ℚ`-trivial pairs that are not doubly transitive.
  - Proposition 13 characterizes the `ℚ`-trivial pairs among the transitive subgroups `G = TH` of
    `AGL(1,q)`, `q = pᵉ`: "(G,H) is Q-trivial if, and only if, the index d divides p−1 and is
    relatively prime to the exponent e". Such a pair is not doubly transitive when `d > 1`.
  - Proposition 14 gives `PSL(2,q)`, `q = 2ᵖ` with `2ᵖ − 1` a prime `≥ 7`, acting on the cosets of
    a dihedral subgroup of order `2(q + 1)`, as `ℚ`-trivial but not doubly transitive.
  - (2′) and (4′), not (2), (3), (4), (5) or (6), are the parts of this entry that apply to such a
    pair, over `ℚ`, once `hirr` is supplied over `ℚ`. No such case is proved here.
- Girstmair 1999 (p. 78) calls the engine well known, citing Huppert, *Endliche Gruppen I*, p. 597,
  Satz 20.2; Girstmair 1982 (p. 86) cites the same page. Dixon (p. 297) cites Curtis–Reiner §32B
  for it.
- Dixon's Theorem 1′ (1997, p. 301) is a later statement of the additive theorem, whose proof Dixon
  omits. Girstmair 1999 (p. 53) also writes that "some minor observations of [11] appear as main
  results in later articles (cf., e.g., [11], Proposition 4, Assertion 3 and [9], Theorem 3)",
  [9] being Drmota–Skałba 1991.
- Girstmair 1982 was read in part (pp. 81, 83, 86 and 97). Huppert, Curtis–Reiner, Drmota–Skałba
  1991, Baron–Drmota–Skałba 1995 and Smyth 1986 were not opened for this entry.
- Background: Smyth (1986), Lemma 1, which Dixon (p. 293) describes as showing "that the existence
  of a nontrivial relation between the roots implies that G does not act as the symmetric group on
  Ω (see Theorem 1 below for a significant generalization)"; and the multiplicative literature
  (Baron–Drmota–Skałba 1995; Zheng 2021). Neither is formalized here.
- The entry contributes a complete kernel-checked proof of the homogeneous case over every field of
  characteristic 0 (and of Dixon's printed form at the roots), and of the criterion forms over
  every field.

**Proved here, from Mathlib.** All eight statements, the two library lemmas behind (6), and the
bridge.
- (1) is proved from scratch by an elementary, character-free stabilizer-averaging argument. Dixon
  (p. 297) cites Curtis–Reiner §32B for the statement only; Curtis–Reiner was not consulted, and
  nothing is claimed about its proof.
- (1) is proved from scratch because Mathlib (at the pin, and at master on 2026-10-28) has no
  irreducibility result for 2-transitive permutation modules. Formalizations in other libraries are
  listed below; nothing is imported from them.

The arguments:
- Proof of (1). Average a nonzero `w ∈ W` over the stabilizer of a point `a`; characteristic 0
  makes `|Stab(a)|` and `|Ω|` invertible in `K`. 2-transitivity makes the average two-valued, and
  genuinely so. So each standard difference `e_b − e_a` lies in `W`, and these span `V₀`.
- Proof of (2′). Apply `hirr` to `W = relModule K α ⊓ V₀`, which is `G`-invariant. If `W ≠ ⊥`, then
  `W = V₀` holds a nonzero zero-sum vector, so `Ω` has two points `a ≠ b`, and
  `e_a − e_b ∈ relModule K α` forces `α a = α b`, contradicting injectivity.
- Proof of (4′). A relation `c` and its translate `x ↦ c (g⁻¹ • x)`, which is a relation by
  `φ g`, have the same coefficient sum. Their difference is a zero-sum relation, so it is `0` by
  (2′). So `c` is `G`-invariant, hence constant by transitivity. No averaging is used, so `K` is
  any field.
- Proofs of (2) and (4). (2′) and (4′), with `hirr` from (1) and, for (4), transitivity from
  2-transitivity.
- Proof of (3). Instantiate (2) with:
  - `G = f.Gal` and `Ω = f.rootSet f.SplittingField`, acted on by Mathlib's
    `Polynomial.Gal.galActionAux`;
  - `α` the inclusion of the root set;
  - `φ g` the Galois automorphism `g` as a `K`-linear map (the compatibility is `rfl`).

  The bound `|Ω| = deg f` comes from `Polynomial.card_rootSet_eq_natDegree`, with separability from
  `Irreducible.separable` (characteristic 0).
- Proofs of (5) and (6). (5) instantiates (4) in the same way. The forward direction of (6)
  applies (2) at the roots to the difference of `c` and each Galois translate, and its reverse
  direction uses that the sum of the roots is Galois-fixed, hence in `K`
  (`IsGalois.of_separable_splitting_field`, `IsGalois.mem_range_algebraMap_iff_fixed`), as
  described under (6) above.

Used from Mathlib and not re-proved:
- the multiple-transitivity API (`MulAction.IsMultiplyPretransitive`, `is_two_pretransitive_iff`)
  and `MulAction.IsPretransitive`;
- the characteristic-0 class `CharZero` and `Nat.cast_ne_zero`;
- the polynomial Galois group (`Polynomial.Gal`) and its action on `Polynomial.rootSet` of
  `Polynomial.SplittingField`;
- `Polynomial.card_rootSet_eq_natDegree` and `Irreducible.separable`;
- `IsGalois.of_separable_splitting_field` and `IsGalois.mem_range_algebraMap_iff_fixed`;
- the `Submodule` span and lattice API;
- for the bridge, `LinearMap.funLeft`, `Subrepresentation` and its lattice, and `IsAtom`.

Their source text at the pinned revision is quoted verbatim, with permalinks, in
`MATHLIB_DEFINITIONS.md`. Kernel-checked facts about them are in `DefinitionAudit.lean`.

## Relation to Dixon's statement

- Dixon's Theorem 1′ has a base field `K`, any subfield of `ℂ`. It concerns relations with
  coefficients in `K` and value in `K`, and its roots lie in `ℂ`.
- Compared statements (2), (3), (4), (5) and (6) take any field `K` of characteristic 0, so every
  subfield of `ℂ`, with value `0` in (2), (3), (4) and (5) and value in `K` in (6), and with the
  roots in Mathlib's abstract `f.SplittingField`; no embedding into `ℂ` is formalized. (2′) and
  (4′) take any field.
- For every subfield `K` of `ℂ` (indeed every field of characteristic 0), Dixon's Theorem 1′, with
  the roots in `f.SplittingField`, is compared statement (6) (value `k ∈ K`, including `k = 0`).
  Its homogeneous case at the roots is compared statement (5) ((4) at the roots), and the
  zero-sum part of that case (value 0, coefficient sum 0) is compared statement (3).
- Dixon (p. 301) defines `U` as the module of coefficient tuples `c` with `∑ c_α α ∈ K`, and says
  that the roots satisfy nontrivial `K`-linear relations if `U ≠ eKG` (`eKG = K·e`, `e` the
  all-ones tuple). (6) is the equality `U = K·e`, both inclusions proved: `U ⊆ K·e` is the
  substance of the theorem, and `K·e ⊆ U`, which Dixon notes always holds, is the fact that the
  sum of the roots lies in `K`.
- The hypothesis `2 ≤ f.natDegree` of (3), (5) and (6) is not in Dixon's Theorem 1′. It excludes
  only `deg f ≤ 1`, where the root set has at most one element, and where the conclusions of (3),
  (5) and (6) hold trivially (a zero-sum tuple on at most one point is `0`, every tuple on at most
  one point is constant, and the root of a polynomial of degree 1 lies in `K`).

## What is not formalized

The **multiplicative** theorem is **not** formalized and **not** claimed: Dixon's Theorem 1(ii)
and, per Zheng 2021, Theorem 3 of Baron–Drmota–Skałba 1995 (not opened). Zheng
(arXiv:1912.07202v1, pp. 1–2), supposing `f ∈ ℚ[x]` irreducible "with no root being a root of
rational" (which excludes `Xᵖ − b`), writes: "by either [1, Theorem 3] or [4, Theorem 1], R_f is
trivial if G_f is 2-transitive on the set of the roots of f", `R_f` being the lattice of
multiplicative relations.
- It concerns multiplicative relations `∏ αᵢ^{mᵢ} ∈ K` among the roots, where 2-transitivity does
  **not** force triviality.
- For example, for a prime `p` and `b ∈ ℚ` not a `p`-th power, `Xᵖ − b` has Galois group
  `AGL(1,p)` over `ℚ`, acting sharply 2-transitively on the roots, and the ratios of its roots are
  `p`-th roots of unity: nontrivial multiplicative relations.
- Dixon's Theorem 1(ii) gives necessary conditions for that exception: `deg f = p` prime, `G`
  isomorphic to the affine group of order `p(p − 1)`, and, if `K ⊆ ℝ` and `deg f > 2`,
  `f = Xᵖ − b`.
- None of this multiplicative content, and none of its `AGL(1,p)`/pure-power exception, is proved
  or claimed.

The **additive** theorem, (2), (3), (4), (5) and (6), carries no such exception, because the
additive module cannot contain any `e_γ − e_δ` (Dixon, p. 301). That is why it, and not the
multiplicative theorem, is what this entry formalizes.

Also not formalized:
- the **2-transitivity of any particular Galois group**. It is a hypothesis in (1), (2), (3), (4),
  (5) and (6), not a theorem of this entry;
- any case of `hirr` other than the 2-transitive one, (1). In particular no primitive pair that is
  not doubly transitive is treated;
- the imprimitive case (Girstmair 1982, Proposition 4, Assertion 1; Girstmair 1999, Proposition
  12, first sentence), and the fact, stated above, that `hirr` forces primitivity for a transitive
  action;
- the 'only if' direction of the criterion (Girstmair 1982, Proposition 4, Assertion 2; Girstmair
  1999, Proposition 12), the character form of its hypothesis, and the converse of Assertion 3
  that Girstmair 1982 states for a splitting field;
- the identification of `Ω → K`, for `K` an extension of `ℚ`, with the scalar extension of
  `Ω → ℚ`. Absolute irreducibility is therefore stated as (1) over an algebraically closed `K`, not
  as a statement about the `ℚ[G]`-module `V₀`. (TauCeti proves the base-change property of the
  augmentation module, `TauCeti.isBaseChange_augmentationScalarMap` in
  `TauCeti/RepresentationTheory/Augmentation/BaseChange.lean`, in Mathlib's `MonoidAlgebra`
  encoding; it is not imported or used here.)

## Prior formalizations

These results come from a search on 2026-10-28 for the six statements (1), (2′), (2), (3), (4′) and
(4) as stated here (over a field `K`, with the criterion forms (2′) and (4′)), at the repository
heads listed below. They are a search result, not a guarantee. Statements (5) and (6) were
searched for on 2026-10-29 (see *Statements (5) and (6)* below).

**The six statements searched.** None of (1), (2′), (2), (3), (4′) and (4), in the form stated
here, was found in any prover. In particular, the general 2-transitive engine stated as a
`K`-submodule of `Ω → K` for every field `K` of characteristic 0, with a character-free proof, and
statements (2′), (2), (3), (4′) and (4), were found in no prover at the repository heads searched.

**Statements (5) and (6).** Statements (5) and (6) were searched for on 2026-10-29: neither was
found in Mathlib master `5cc3cb8e30d468f57415b3eecae890d47fcc329d`, TauCeti
`c2ff0693cf399626a66a47f72c62bb37c2b2ff57`, openai/math `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`,
oqp-batch-2026 `da37af2ae174687403fbd97e9673c819edee71fd`, math-comp
`cc79906a9478f4efd11062ac49679176dd5132e8`, odd-order `ba734c020d9f7dce5758fa822904dea29e2624ba` or
AxiomMath/CFSG `69cb972f587a3ecc035e092253167ff2e303c962` (full-text search), nor in the AFP
`4bba12205aaf1ec15c2fbd8b716fe511083c1e6d` (GitHub code search and file listings). The Lean Zulip,
the Lean Reservoir index, Mizar, Agda, HOL Light and Metamath were not reached for them.
Qiuzhen-CFSG/CFSG, keithadler/saxl-lean and QuAIR/Lean-QIT were not re-searched for them. The fact
behind the reverse direction of (6), that the sum of the roots lies in the base field, is in
Mathlib at the pin in Vieta form (`Polynomial.Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`)
and, multiplied by the leading coefficient, as the case `q = X` of
`Polynomial.leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap`, both for the
multiset of roots; `BDS.exists_sum_rootSet_eq_algebraMap` states it for the root set of a
separable polynomial and proves it by Galois invariance.

**The engine (1)** is formalized in part elsewhere.
* **TauCeti** (Apache-2.0, since PR #2030 on 2026-08-05). File
  `TauCeti/RepresentationTheory/Symmetric/Standard.lean`. This is the `Sₙ` case of (1), in
  augmentation form, over `ℚ` among other fields.
  - For `Sₙ` acting on `α`, over any division ring, with `2 ≤ |α|` and `|α| = 2 ∨ |α| ≠ 0`, the
    augmentation subrepresentation of `Representation.ofMulAction` is an atom
    (`TauCeti.isAtom_augmentationSubrepresentation`).
  - Over a field, under the same hypotheses, the standard representation is irreducible
    (`TauCeti.isIrreducible_standardRepresentation`).
  - Separately, `TauCeti.is_two_pretransitive_iff_irreducible_divByMonic`
    (`TauCeti/FieldTheory/GaloisGroups/MultipleTransitivity.lean`) states 2-transitivity of a Galois
    root action with the same encoding as (3): `IsMultiplyPretransitive p.Gal (p.rootSet
    p.SplittingField) 2`.
* **AxiomMath/CFSG** (Apache-2.0, public since 2026-10-27). This is the general 2-transitive engine
  in character form over `ℂ`, with its converse. It is not the submodule form of (1), and it is the
  closest item found.
  - `CFSG.permutation_character_orbit_count` (`CFSG/CharacterTheory/PermutationCharacterOrbits.lean`)
    covers every finite `W` acting transitively on a finite `I` with `2 ≤ |I|`. Its conclusion:
    `IsMultiplyPretransitive W I 2` holds iff the permutation character minus `1` is the character
    of an irreducible complex representation.
  - The same library also defines `CFSG.Wreathed.CentralSL2.sumZeroSubmodule` and `sumZeroSubrep`
    (`CFSG/CharacterTheory/Wreathed/CentralSL2/SumZero.lean`): the zero-sum subspace of `I → ℂ`
    under `f ↦ f (w⁻¹ • i)`, that is, `V₀` over `ℂ` with the action used here, together with
    `sumZeroSubrep_character` (character = fixed points − 1). Combined with
    `permutation_character_orbit_count`, this would give the `ℂ` case of (1) in submodule form in a
    few lines, but no theorem stating that was found.
  - `CFSG.Semidihedral.Principal.doubly_transitive_prime_divisible_degree_principal_augmentation`
    (`CFSG/CharacterTheory/Semidihedral/Principal/DoublyTransitiveAugmentation.lean`) gives, for a
    2-transitive action with `p ∣ |Ω|`, an irreducible complex representation with character fixed
    points − 1 in the principal `p`-block (character form, `ℂ`, under a divisibility hypothesis).
* **openai/math** (Apache-2.0). This proves irreducibility of every Specht module of `Sₙ` over `ℂ`;
  for shape `(n−1, 1)` that gives the `Sₙ` case of (1) over `ℂ`. Its declarations:
  - `OAI.Saxl.specht_irreducible` (`lean/OAI/RepresentationTheory/Saxl/SpechtSubmodule.lean`);
  - the instance `OAI.PartialPermutation.YoungTabloid.specht_irreducible`
    (`lean/OAI/RepresentationTheory/PartialPermutation/SpechtModules.lean`);
  - `OAI.CubeShuffle.Specht.representation_irreducible`
    (`lean/OAI/RepresentationTheory/YoungSymmetry/Polytabloid.lean`), with
    `labelledRepresentation_irreducible` in `.../YoungSymmetry/Irreducible.lean`;
  - other developments in the same corpus.

  These are stated for Specht modules of `Sₙ`, not for 2-transitive groups.
* **Qiuzhen-CFSG/CFSG** has `BinaryPermutation.alternatingNatural_isIrreducible`, for `Aₙ`,
  `n ≥ 5`, over `ZMod 2`: characteristic 2 and `Aₙ`-specific, not (1).

Nothing is imported from any of the libraries above.

The remaining building blocks are scattered but unjoined:
- Mathlib has the permutation representation `Representation.ofMulAction`, char-0 semisimplicity
  (`Maschke`), Schur (`RepresentationTheory.Irreducible`), the 2-transitivity predicate
  `MulAction.IsMultiplyPretransitive` and the Galois-group-as-permutations action
  (`Polynomial.Gal.galActionHom`).
- Coq/mathcomp has the `ntransitive` predicate and a full character library.
- Isabelle/AFP `Rep_Fin_Groups` has Maschke, Schur and Frobenius reciprocity.

Repository heads searched on 2026-10-28 for the six statements (1), (2′), (2), (3), (4′) and (4)
as stated here:

| System | Repository | Commit |
|---|---|---|
| Lean 4 + Mathlib | leanprover-community/mathlib4 `master` (and open PRs) | `8fe7ce475b056f0b266d7107893f2c4d772c712f` |
| Lean 4 + Mathlib | mathlib4 at the pin | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Lean | TauCetiProject/TauCeti | `e6b5f42c62ab0484faf5c0e66079de65bcc138a2` |
| Lean | AxiomMath/CFSG | `69cb972f587a3ecc035e092253167ff2e303c962` |
| Lean | Qiuzhen-CFSG/CFSG | `0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7` |
| Lean | openai/math | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` |
| Lean | physical-superintelligence/oqp-batch-2026 | `da37af2ae174687403fbd97e9673c819edee71fd` |
| Lean | keithadler/saxl-lean | `b90189df81c4a14041e4b49bda7333a590be3e0d` |
| Isabelle/AFP | isabelle-prover/mirror-afp-devel | `4bba12205aaf1ec15c2fbd8b716fe511083c1e6d` |
| Coq/Rocq | math-comp/math-comp `master` | `cc79906a9478f4efd11062ac49679176dd5132e8` |
| Coq/Rocq | math-comp/odd-order `master` | `ba734c020d9f7dce5758fa822904dea29e2624ba` |

Searched earlier the same day, for the statements as they were then stated over `ℚ`, and not
re-searched individually for the current forms:

| System | Repository | Commit |
|---|---|---|
| Lean | QuAIR/Lean-QIT | `8a931d4bda61ba503cfc0728704cfef5dedf2cff` |
| HOL Light | jrh13/hol-light `master` | `d30e8239887b2348a063f82232a864de1cc2df15` |
| Metamath | metamath/set.mm `develop` | `b975dbbd636372803f3102045aa333771f25a477` |

Notes on the search:
- A GitHub-wide code search (Lean and unrestricted) was also run for the current statements, with
  terms including `IsMultiplyPretransitive` together with `IsIrreducible`, `augmentation` or
  `rootSet`, "doubly transitive" or "2-transitive" with "irreducible", and `Girstmair`. It covers
  default branches only, and indexing of very large repositories may be partial.
- Mizar/MML, Agda, the Lean Reservoir index and the Lean Zulip were not reached.

## Layout and build

* `Challenge.lean` — the eight statements with placeholder proofs, after the entry's definitions
  (between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`). It imports Mathlib only.
* `BDS/Defs.lean` — the same definitions (`zeroSum`, `relModule`), byte for byte. The proof modules
  are built on it.
* `BDS/TwoTransitiveIrreducible.lean` — the engine (1), `BDS.zeroSum_irreducible`, with the
  character-free stabilizer-averaging proof.
* `BDS/AdditiveRelations.lean` — the additive theorem (homogeneous case over `K`): the criterion
  forms `BDS.additive_core_of_irreducible` (2′) and `BDS.relModule_le_span_one_of_irreducible`
  (4′), and the 2-transitive forms `BDS.additive_core` (2), `BDS.relModule_le_span_one` (4) and
  `BDS.additive_roots_no_relation` (3).
* `BDS/RootsCorollaries.lean` — `BDS.relModule_roots_le_span_one` (5) and
  `BDS.roots_inhomogeneous_iff_const` (6), at the roots, with the two library lemmas the latter
  combines: `BDS.roots_inhomogeneous_const` (its forward direction) and
  `BDS.exists_sum_rootSet_eq_algebraMap` (the sum of the roots of a separable polynomial lies in
  the base field).
* `BDS/AtomBridge.lean` — the uncompared bridge to Mathlib's lattice of subrepresentations.
* `BDS.lean` — the library index.
* `Solution.lean` — the same eight statements, each proved by one application of the theorem of the
  same name in namespace `BDS`.
* `comparator.json` — the eight compared declarations, in order, and the permitted axioms.
* `DefinitionAudit.lean` — a default build target. It imports Mathlib only and is not compared. It
  holds kernel-checked facts about the Mathlib definitions the statements use: the 2-transitivity
  predicate, characteristic 0, the permutation representation, the Galois action on the root set
  and its instance, the root count, separability, and the submodule span and lattice.
* `MATHLIB_DEFINITIONS.md` — those Mathlib definitions, quoted verbatim at the pinned revision with
  path, line range and permalink.
* `formalization.yaml` — sources, classification and disclosure.
* `BUILD.txt` — the build and axiom record: toolchain, Mathlib revision, warnings by file,
  `#print axioms` for the eight compared declarations, the eight `BDS` theorems they apply, the two
  further library lemmas behind (6), the two bridge theorems and the thirteen `DefinitionAudit`
  theorems, the comparator verdict, and file hashes.
* `SHA256SUMS.txt` — the `.lean` file hashes.

The proof modules began as the author's earlier kernel-checked development over `ℚ`, split into
the library layout above and given module-system headers. They were generalized to a field `K`,
and the criterion forms (2′) and (4′) were added, on 2026-10-28. Statement (5), proved in the
library on 2026-10-28, was added to the compared set on 2026-10-29 with its statement and proof
unchanged. Statement (6) was added the same day: its forward direction is the library theorem
`BDS.roots_inhomogeneous_const` of 2026-10-28, and its reverse direction the lemma
`BDS.exists_sum_rootSet_eq_algebraMap`, added on 2026-10-29.

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```
lake exe cache get
lake build
```

## References

- K. Girstmair, "Linear dependence of zeros of polynomials and construction of primitive elements",
  *Manuscripta Math.* 39 (1982), 81–97. doi:10.1007/BF01312446. Free scan: GDZ Göttingen, via
  EuDML doc 154873. Proposition 1 (p. 83): the relation module of a root is a submodule of
  `K(G/H)` "belonging to H". Proposition 4 (p. 86): Assertion 1, imprimitive pairs admit
  non-trivial relations; Assertion 2, the criterion (module form, primitive pairs); Assertion 3,
  doubly transitive pairs admit only trivial relations; all for `char(K)` prime to `|G|`. Read in
  part (pp. 81, 83, 86 and 97).
- K. Girstmair, "Linear relations between roots of polynomials", *Acta Arith.* 89 (1999), 53–96.
  doi:10.4064/aa-89-1-53-96. Section 4: "K-trivial" pairs. On p. 78: Definition 7; Proposition 12,
  the criterion in character form, "essentially contained in Proposition 4 of [11]"; double
  transitivity implies K-triviality over every characteristic-0 field `K`; where the additive case
  was observed; the engine as well known. On p. 53: later appearances of results of the 1982 paper.
- J. D. Dixon, "Polynomials with nontrivial relations between their roots", *Acta Arith.* 82 (1997),
  293–302. doi:10.4064/aa-82-3-293-302. Theorem 1′ (p. 301), the additive theorem, with the proof
  omitted. The engine is cited on p. 297.
- B. Huppert, *Endliche Gruppen I*, Springer (1967). doi:10.1007/978-3-642-64981-3. p. 597,
  Satz 20.2, as cited by Girstmair 1999 (p. 78): the engine, absolute irreducibility iff double
  transitivity. Not opened.
- C. W. Curtis, I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  Interscience/Wiley (1962), §32B. The engine, as cited by Dixon on p. 297. Not opened.
- M. Drmota, M. Skałba, "On multiplicative and linear independence of polynomial roots",
  *Contributions to General Algebra* 7 (1991), 127–135. Theorem 3, as cited by Girstmair 1999
  (p. 53). Background; not opened.
- G. Baron, M. Drmota, M. Skałba, "Polynomial relations between polynomial roots", *J. Algebra* 177
  (1995), 827–846. doi:10.1006/jabr.1995.1330. Theorem 3, on the multiplicative side per Zheng
  2021 (p. 2); **not** formalized here. Not opened.
- C. J. Smyth, "Additive and multiplicative relations connecting conjugate algebraic numbers",
  *J. Number Theory* 23 (1986), 243–254. doi:10.1016/0022-314X(86)90094-6. Lemma 1, as described
  by Dixon (p. 293). Background; not opened.
- T. Zheng, "A fast algorithm for computing multiplicative relations between the roots of a generic
  polynomial", *J. Symbolic Comput.* 104 (2021), 381–401. doi:10.1016/j.jsc.2020.08.001. Preprint:
  arXiv:1912.07202, "Computing Multiplicative Relations between Roots of a Polynomial". The
  multiplicative side; background.

## Licence

MIT (see `LICENSE`). The Mathlib API it builds on is Apache-2.0, copyright the Mathlib authors.
