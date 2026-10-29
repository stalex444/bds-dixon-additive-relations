module
public import Mathlib

@[expose] public section
/-!
# Audit of the imported definitions

The compared statements in `Challenge.lean` rest on definitions imported from Mathlib (pinned
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`): the 2-transitivity predicate
`MulAction.IsMultiplyPretransitive` and the transitivity predicate `MulAction.IsPretransitive`,
the characteristic-0 class `CharZero`, the permutation representation `Representation.ofMulAction`,
the Galois group `Polynomial.Gal` and its action `Polynomial.Gal.galActionAux` on the root set
`Polynomial.rootSet` of the splitting field `Polynomial.SplittingField`, the root count
`Polynomial.card_rootSet_eq_natDegree`, separability of irreducibles over a characteristic-zero
field (`Irreducible.separable`), the submodule span of a singleton, and the lattice operations on
`Submodule`. Their pinned source text is quoted verbatim, with path, line range and a permalink at
the pinned revision, in `MATHLIB_DEFINITIONS.md`. This file imports Mathlib only and is not part of
the compared set. It records, as kernel-checked theorems, the facts about those
definitions that the informal account relies on, so that the correspondence can be audited from this
repository alone. Every statement that involves a coefficient field is over an arbitrary field
`K` (of characteristic 0 in `irreducible_separable` and `charZero_cast_ne_zero`); the three
`Submodule` lattice facts are over any semiring, and the two transitivity facts involve no
scalars:

* `two_pretransitive_iff` — `IsMultiplyPretransitive G Ω 2` means the action is 2-transitive in the
  elementary sense: for any `a ≠ b` and `c ≠ d` there is `g` with `g • a = c` and `g • b = d`. This
  is the hypothesis of compared statements (1), (2), (3), (4), (5) and (6).
* `isPretransitive_of_two` — a 2-transitive action is transitive (used passing from (1) to the span
  of standard differences, from (4′) to (4), and in the proof of (6)).
* `irreducible_separable` — over a characteristic-zero field `K` an irreducible polynomial is
  separable (so an irreducible `f : K[X]` is separable: the hypothesis of (3), (5) and (6) feeding
  the root count).
* `charZero_cast_ne_zero` — in a field of characteristic 0 a nonzero natural number is nonzero:
  the only use of `CharZero K` in the engine (1), which inverts the cardinalities `|Stab(a)|` and
  `|Ω|`.
* `card_rootSet` — a separable polynomial over `K` that splits over `L` has exactly `natDegree`
  roots in `L`: the root set `Ω = f.rootSet f.SplittingField` of (3), (5) and (6) has
  `|Ω| = deg f`, so `deg f ≥ 2` gives `2 ≤ |Ω|`.
* `gal_instance_eq` — the `MulAction f.Gal (f.rootSet f.SplittingField)` instance that statements
  (3), (5) and (6) elaborate against is `Polynomial.Gal.galActionAux f` (`rfl`).
* `gal_smul_coe` — the Galois action on the root set is application of the field automorphism:
  `↑(g • r) = g ↑r`. This is exactly why the `K`-linear compatibility `φ g (α x) = α (g • x)` used
  for (3), (5) and (6), with `φ g` the automorphism `g` and `α` the inclusion of the root set, holds
  by `rfl`.
* `mem_span_singleton` — `x ∈ K ∙ y ↔ ∃ a, a • y = x`: membership in the line spanned by a single
  tuple, the right-hand side of (4), (4′) and (5) (`relModule K α ≤ K ∙ (fun _ => 1)`).
* `ofMulAction_single` — the permutation representation `Representation.ofMulAction K G Ω` sends the
  basis vector `MonoidAlgebra.single x r` to `MonoidAlgebra.single (g • x) r`.
* `coeff_ofMulAction` — the coefficients of `ofMulAction K G Ω g f` are
  `(ofMulAction K G Ω g f).coeff x = f.coeff (g⁻¹ • x)`: the action formula `(g • f) x = f (g⁻¹ • x)`
  modeled here on `Ω → K`, read through `MonoidAlgebra.coeff` (documented in
  `BDS/TwoTransitiveIrreducible`).
* `ne_bot_iff`, `mem_inf`, `mem_bot` — the `Submodule` lattice facts used in the engine and its
  application: a nonzero submodule has a nonzero element; `x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V`; and
  `x ∈ ⊥ ↔ x = 0`.

Each theorem is a restatement of the named Mathlib theorem or a `rfl`; none uses anything from this
entry.
-/

namespace DefinitionAudit

open MulAction Polynomial

/-- `IsMultiplyPretransitive G Ω 2` is 2-transitivity in the elementary sense (Mathlib's
`MulAction.is_two_pretransitive_iff`, restated). -/
theorem two_pretransitive_iff {G Ω : Type*} [Group G] [MulAction G Ω] :
    IsMultiplyPretransitive G Ω 2 ↔
      ∀ {a b c d : Ω}, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d :=
  is_two_pretransitive_iff

/-- A 2-transitive action is transitive (Mathlib's
`MulAction.isPretransitive_of_is_two_pretransitive`, restated). -/
theorem isPretransitive_of_two {G Ω : Type*} [Group G] [MulAction G Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) : IsPretransitive G Ω :=
  have := h2
  isPretransitive_of_is_two_pretransitive

/-- Over a characteristic-zero field an irreducible polynomial is separable (Mathlib's
`Irreducible.separable`); in particular an irreducible `f : K[X]` is separable. -/
theorem irreducible_separable {K : Type*} [Field K] [CharZero K] {f : K[X]} (hf : Irreducible f) :
    f.Separable :=
  hf.separable

/-- In a field of characteristic 0 the cast of a nonzero natural number is nonzero (Mathlib's
`Nat.cast_ne_zero`, restated): what lets the engine (1) invert `|Stab(a)|` and `|Ω|` in `K`. -/
theorem charZero_cast_ne_zero {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : n ≠ 0) :
    (n : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr hn

/-- A separable polynomial that splits over `L` has exactly `natDegree` roots in `L` (Mathlib's
`Polynomial.card_rootSet_eq_natDegree`), so the root set `f.rootSet f.SplittingField` of an
irreducible `f` over a field of characteristic 0 has `deg f` elements. -/
theorem card_rootSet {K : Type*} [Field K] {f : K[X]} (hsep : f.Separable)
    (hsplit : (f.map (algebraMap K f.SplittingField)).Splits) :
    Fintype.card (f.rootSet f.SplittingField) = f.natDegree :=
  card_rootSet_eq_natDegree hsep hsplit

/-- The `MulAction` instance on the root set that statements (3), (5) and (6) use is Mathlib's
`Polynomial.Gal.galActionAux` (`rfl`); `Polynomial.Gal.galAction` would need a `Fact (Splits …)`
instance, which `f.SplittingField` does not carry. -/
theorem gal_instance_eq {K : Type*} [Field K] (f : K[X]) :
    (inferInstance : MulAction f.Gal (f.rootSet f.SplittingField)) = Polynomial.Gal.galActionAux f :=
  rfl

/-- The Galois action on the root set is application of the field automorphism: `↑(g • r) = g ↑r`
(`rfl`). This is why the `K`-linear compatibility used for statements (3), (5) and (6) is `rfl`. -/
theorem gal_smul_coe {K : Type*} [Field K] (f : K[X]) (g : f.Gal)
    (r : f.rootSet f.SplittingField) :
    ((g • r : f.rootSet f.SplittingField) : f.SplittingField) = g r :=
  rfl

/-- Membership in the line spanned by a single vector (Mathlib's `Submodule.mem_span_singleton`):
`x ∈ K ∙ y ↔ ∃ a, a • y = x`. The right-hand side of statements (4), (4′) and (5). -/
theorem mem_span_singleton {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x y : M) :
    x ∈ Submodule.span K {y} ↔ ∃ a : K, a • y = x :=
  Submodule.mem_span_singleton

/-- The permutation representation sends a basis vector to a basis vector (Mathlib's
`Representation.ofMulAction_single`): `ofMulAction K G Ω g (single x r) = single (g • x) r`. The
`MonoidAlgebra K Ω` incarnation of the action modeled here on `Ω → K`. -/
theorem ofMulAction_single {K G Ω : Type*} [Field K] [Monoid G] [MulAction G Ω] (g : G) (x : Ω)
    (r : K) :
    Representation.ofMulAction K G Ω g (MonoidAlgebra.single x r) = MonoidAlgebra.single (g • x) r :=
  Representation.ofMulAction_single g x r

/-- The coefficients of the permutation representation (Mathlib's
`Representation.coeff_ofMulAction`): `(ofMulAction K G Ω g f).coeff x = f.coeff (g⁻¹ • x)`, the
action formula `(g • f) x = f (g⁻¹ • x)` modeled here on `Ω → K`. -/
theorem coeff_ofMulAction {K G Ω : Type*} [Field K] [Group G] [MulAction G Ω] (g : G)
    (f : MonoidAlgebra K Ω) (x : Ω) :
    (Representation.ofMulAction K G Ω g f).coeff x = f.coeff (g⁻¹ • x) :=
  Representation.coeff_ofMulAction g f x

/-- A nonzero submodule has a nonzero element (Mathlib's `Submodule.ne_bot_iff`). -/
theorem ne_bot_iff {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) : N ≠ ⊥ ↔ ∃ x ∈ N, x ≠ 0 :=
  Submodule.ne_bot_iff N

/-- The meet of two submodules (Mathlib's `Submodule.mem_inf`): `x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V`. -/
theorem mem_inf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {U V : Submodule R M} {x : M} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Submodule.mem_inf

/-- The bottom submodule is the zero subspace (Mathlib's `Submodule.mem_bot`): `x ∈ ⊥ ↔ x = 0`. -/
theorem mem_bot {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (x : M) :
    x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Submodule.mem_bot R

end DefinitionAudit
