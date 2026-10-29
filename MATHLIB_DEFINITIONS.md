# Mathlib definitions used by the compared statements

The compared statements of `Challenge.lean` rest on two definitions of this entry, `BDS.zeroSum` and `BDS.relModule`. These are stated in `Challenge.lean` between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`. Beyond them, the statements rest on Mathlib declarations. Quoted below are those declarations, the Mathlib theorems the informal account cites, the representation-theoretic definitions used to document the modeling, and the Mathlib declarations the uncompared bridge `BDS/AtomBridge.lean` states its result in (see **Scope**).

Pinned revision: `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Toolchain: `leanprover/lean4:v4.35.0-rc2`.

How each entry was produced:
- **Location.** The module and the line range are the declaration's own range, as reported by Lean (`findDeclarationRanges?`) in this package's build environment. The range includes the docstring and attributes.
- **Text.** The quoted text is lines `a`–`b` of `https://raw.githubusercontent.com/leanprover-community/mathlib4/065356127b1dc0016f66b7283ce0ce2c4055aa55/<path>`. It was checked byte for byte against that raw file, and against this package's pinned checkout, on 2026-10-28 (the two `IsGalois` entries on 2026-10-29).
- **Permalink.** Each permalink is a GitHub blob URL at the pinned revision; each returned HTTP 200 on 2026-10-28 (the two `IsGalois` entries on 2026-10-29).

`DefinitionAudit.lean` is a default build target. It imports Mathlib only and is not compared. It records, as kernel-checked theorems, the facts about these declarations that the informal account relies on; each entry names the matching audit theorem.

**Scope.** The quoted declarations are:
- every Mathlib definition and instance specific to the eight statements, that is, named in or elaborated by their hypotheses and conclusions, other than the foundational infrastructure listed below;
- the representation-theoretic definitions used to document the modeling, and those used by the uncompared bridge `BDS/AtomBridge.lean`;
- the Mathlib theorems the informal account cites.

Not quoted: the foundational infrastructure common to all of Mathlib. This covers the `Field` class (the coefficient field `K` of all eight statements), `Fintype`, `Fintype.card`, `DecidableEq`, the `Group` and `MulAction` classes, `Finset.sum` (`∑`), `Module`, `AddCommGroup`, `LinearMap` (`→ₗ`), `AlgEquiv` (`≃ₐ`), `Function.Injective`, `Fin`, the polynomial type `Polynomial` (`K[X]`, in statements (3), (5) and (6)), the order `≤` on submodules, and the field instance on `SplittingField`, its `K`-algebra instance and the algebra map `algebraMap` (through which `c r • r` in statements (3), (5) and (6), and the value `algebraMap K f.SplittingField k` in statement (6), elaborate).

The Mathlib source is Apache-2.0, copyright the Mathlib authors.

## The 2-transitivity and transitivity hypotheses (statements (1), (2), (3), (4), (4′), (5) and (6))

### `MulAction.IsMultiplyPretransitive`

The hypothesis `IsMultiplyPretransitive G Ω 2` of statements (1), (2), (3), (4), (5) and (6): the action on `Fin 2 ↪ Ω` is pretransitive.

`Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean`, lines 116–120: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean#L116-L120

```lean
/-- An action of a group on a type `α` is `n`-pretransitive
if the associated action on `Fin n ↪ α` is pretransitive. -/
@[to_additive /-- An additive action of an additive group on a type `α`
is `n`-pretransitive if the associated action on `Fin n ↪ α` is pretransitive. -/]
abbrev IsMultiplyPretransitive (n : ℕ) := IsPretransitive G (Fin n ↪ α)
```

### `MulAction.IsPretransitive`

Pretransitivity, in terms of which `IsMultiplyPretransitive` is an `abbrev`. It is also the transitivity hypothesis `htr : IsPretransitive G Ω` of statement (4′).

`Mathlib/Algebra/Group/Action/Pretransitive.lean`, lines 57–62: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Action/Pretransitive.lean#L57-L62

```lean
/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive (attr := mk_iff)]
class MulAction.IsPretransitive (M α : Type*) [SMul M α] : Prop where
  /-- There is `g` such that `g • x = y`. -/
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y
```

### `Function.Embedding`

The type `Fin 2 ↪ Ω` of injective maps.

`Mathlib/Logic/Embedding/Basic.lean`, lines 25–30: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Embedding/Basic.lean#L25-L30

```lean
/-- `α ↪ β` is a bundled injective function. -/
structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun
```

### `Function.Embedding.smul`

The `G`-action on `Fin 2 ↪ Ω` (post-composition), the `SMul` part.

`Mathlib/GroupTheory/GroupAction/Embedding.lean`, lines 31–33: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/Embedding.lean#L31-L33

```lean
@[to_additive]
instance smul [Group G] [MulAction G β] : SMul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩
```

### `Function.Embedding.instMulAction`

The `MulAction G (Fin 2 ↪ Ω)` instance that the hypothesis elaborates against.

`Mathlib/GroupTheory/GroupAction/Embedding.lean`, lines 61–63: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/Embedding.lean#L61-L63

```lean
@[to_additive]
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  DFunLike.coe_injective.mulAction _ coe_smul
```

### `MulAction.is_two_pretransitive_iff`

The elementary unfolding (audit: `two_pretransitive_iff`).

`Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean`, lines 204–226: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean#L204-L226

```lean
/-- An action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/
@[to_additive /-- An additive action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/]
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive G α 2 ↔
      ∀ {a b c d : α} (_ : a ≠ b) (_ : c ≠ d), ∃ g : G, g • a = c ∧ g • b = d := by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']
```

### `MulAction.isPretransitive_of_is_two_pretransitive`

2-transitive ⇒ transitive (audit: `isPretransitive_of_two`); used to pass from (4′) to (4), and in the proof of (6).

`Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean`, lines 228–237: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean#L228-L237

```lean
/-- A `2`-pretransitive action is pretransitive. -/
@[to_additive /-- A `2`-pretransitive additive action is pretransitive. -/]
theorem isPretransitive_of_is_two_pretransitive
    [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α where
  exists_smul_eq a b := by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩
```

### `MulAction.stabilizer`

The point stabilizer, over which the proof of (1) averages (used in the proof, not in a statement).

`Mathlib/GroupTheory/GroupAction/Defs.lean`, lines 511–517: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/GroupAction/Defs.lean#L511-L517

```lean
/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive /-- The stabilizer of an element under an action, i.e. what sends the element to
itself. An additive subgroup. -/]
def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }
```

## Characteristic 0 (statements (1), (2), (3), (4), (5) and (6))

### `CharZero`

The hypothesis `[CharZero K]` of statements (1), (2), (3), (4), (5) and (6); statements (2′) and (4′) do not carry it.

`Mathlib/Algebra/CharZero/Defs.lean`, lines 32–45: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/CharZero/Defs.lean#L32-L45

```lean
/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.)

*Warning*: for a semiring `R`, `CharZero R` and `CharP R 0` need not coincide.
* `CharZero R` requires an injection `ℕ ↪ R`;
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.
  For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
  `CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
  This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : ℕ → R)
```

### `Nat.cast_ne_zero`

In characteristic 0 a nonzero natural number is nonzero in `K`: the only use of `CharZero K` in the proof of (1), which inverts `|Stab(a)|` and `|Ω|` (audit: `charZero_cast_ne_zero`).

`Mathlib/Algebra/CharZero/Defs.lean`, lines 73–75: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/CharZero/Defs.lean#L73-L75

```lean
@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
```

## The concrete instantiation at the roots (statements (3), (5) and (6))

### `Polynomial.Gal`

`f.Gal`, the Galois group `f.SplittingField ≃ₐ[K] f.SplittingField`.

`Mathlib/FieldTheory/PolynomialGaloisGroup.lean`, lines 55–58: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/PolynomialGaloisGroup.lean#L55-L58

```lean
/-- The Galois group of a polynomial. -/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField
```

### `Polynomial.Gal.galActionAux`

The `MulAction f.Gal (f.rootSet f.SplittingField)` instance statements (3), (5) and (6) elaborate against (audit: `gal_instance_eq`, `gal_smul_coe`).

`Mathlib/FieldTheory/PolynomialGaloisGroup.lean`, lines 158–161: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/PolynomialGaloisGroup.lean#L158-L161

```lean
instance galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where
  smul ϕ := Set.MapsTo.restrict ϕ _ _ <| rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
```

### `Polynomial.Gal.galAction`

Quoted to show that it is NOT the instance used: it requires `Fact (Splits …)`, which `f.SplittingField` does not carry at the pin.

`Mathlib/FieldTheory/PolynomialGaloisGroup.lean`, lines 175–179: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/PolynomialGaloisGroup.lean#L175-L179

```lean
/-- The action of `gal p` on the roots of `p` in `E`. -/
instance galAction [Fact ((p.map (algebraMap F E)).Splits)] : MulAction p.Gal (rootSet p E) where
  one_smul _ := by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.symm_apply_apply, mul_smul]
```

### `Polynomial.SplittingField`

`f.SplittingField`.

`Mathlib/FieldTheory/SplittingField/Construction.lean`, lines 211–216: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/SplittingField/Construction.lean#L211-L216

```lean
/-- A splitting field of a polynomial. -/
@[stacks 09HV "The construction of the splitting field."]
def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited
```

### `Polynomial.SplittingField.splits`

`f` splits in `f.SplittingField` (used in the proofs of (3), (5) and (6)).

`Mathlib/FieldTheory/SplittingField/Construction.lean`, lines 272–274: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/SplittingField/Construction.lean#L272-L274

```lean
@[stacks 09HU "Splitting part"]
protected theorem splits : Splits (f.map (algebraMap K (SplittingField f))) :=
  IsSplittingField.splits f.SplittingField f
```

### `Polynomial.rootSet`

`f.rootSet f.SplittingField`, the set `Ω` of (3), (5) and (6).

`Mathlib/Algebra/Polynomial/Roots.lean`, lines 574–580: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Roots.lean#L574-L580

```lean
/-- The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset
```

### `Polynomial.rootSetFintype`

The `Fintype` instance on the root set, used by the sums `∑ r, …` in (3) and (6), and by `relModule` in (5).

`Mathlib/Algebra/Polynomial/Roots.lean`, lines 605–607: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Roots.lean#L605-L607

```lean
instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _
```

### `Polynomial.card_rootSet_eq_natDegree`

`|Ω| = deg f` for a separable split polynomial (audit: `card_rootSet`).

`Mathlib/FieldTheory/Separable.lean`, lines 442–447: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Separable.lean#L442-L447

```lean
theorem card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable)
    (hsplit : Splits (p.map (algebraMap F K))) : Fintype.card (p.rootSet K) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map), ← hsplit.natDegree_eq_card_roots,
    natDegree_map]
```

### `Irreducible`

The hypothesis `Irreducible f` of (3), (5) and (6).

`Mathlib/Algebra/Group/Irreducible/Defs.lean`, lines 39–48: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Irreducible/Defs.lean#L39-L48

```lean
/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements. -/
@[to_additive (attr := wikidata Q2989575)]
structure Irreducible (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible element factors, then one factor is a unit. -/
  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b → IsUnit a ∨ IsUnit b
```

### `Irreducible.separable`

Irreducible ⇒ separable over a characteristic-zero field `K` (audit: `irreducible_separable`).

`Mathlib/FieldTheory/Separable.lean`, lines 510–514: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Separable.lean#L510-L514

```lean
theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable := by
  rw [separable_iff_derivative_ne_zero hf, Ne, ← degree_eq_bot, degree_derivative]
  · rintro ⟨⟩
  exact hf.natDegree_pos.ne'
```

### `IsGalois.of_separable_splitting_field`

The splitting field of a separable polynomial is Galois over the base field. Used in the proof of the reverse direction of (6) (`BDS.exists_sum_rootSet_eq_algebraMap`): the splitting field of the separable `f` is Galois over `K`.

`Mathlib/FieldTheory/Galois/Basic.lean`, lines 534–537: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Galois/Basic.lean#L534-L537

```lean
theorem of_separable_splitting_field [p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E :=
  { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field F E hp,
    to_normal := Normal.of_isSplittingField p }
```

### `IsGalois.mem_range_algebraMap_iff_fixed`

In a finite Galois extension, an element fixed by every automorphism lies in the base field. Used in the same proof: the sum of the roots, fixed by every automorphism, lies in `K`.

`Mathlib/FieldTheory/Galois/Basic.lean`, lines 338–342: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Galois/Basic.lean#L338-L342

```lean
/-- See `InfiniteGalois.mem_range_algebraMap_iff_fixed` for the infinite case,
i.e. without the `[FiniteDimensional F E]` assumption. -/
theorem mem_range_algebraMap_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔ ∀ f : Gal(E/F), f x = x :=
  mem_bot_iff_fixed x
```

### `Polynomial.natDegree`

The hypothesis `2 ≤ f.natDegree` of (3), (5) and (6).

`Mathlib/Algebra/Polynomial/Degree/Defs.lean`, lines 51–53: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Degree/Defs.lean#L51-L53

```lean
/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0
```

### `Polynomial.degree`

`natDegree` is defined from `degree`.

`Mathlib/Algebra/Polynomial/Degree/Defs.lean`, lines 45–49: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Degree/Defs.lean#L45-L49

```lean
/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : R[X]) : WithBot ℕ :=
  p.support.max
```

## Submodules and the span-one target (statements (1), (2′), (2), (4′), (4), (5))

### `Submodule`

The type of `W`, `zeroSum K Ω` and `relModule K α`.

`Mathlib/Algebra/Module/Submodule/Defs.lean`, lines 38–42: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Defs.lean#L38-L42

```lean
/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M
```

### `Submodule.instBot`

`⊥`, as in the hypothesis `W ≠ ⊥` of (1) and inside the hypothesis `hirr` of (2′) and (4′).

`Mathlib/Algebra/Module/Submodule/Lattice.lean`, lines 51–55: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L51-L55

```lean
/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩
```

### `Submodule.mem_bot`

`x ∈ ⊥ ↔ x = 0` (audit: `mem_bot`).

`Mathlib/Algebra/Module/Submodule/Lattice.lean`, lines 73–75: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L73-L75

```lean
@[simp]
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff
```

### `Submodule.ne_bot_iff`

A nonzero submodule has a nonzero element (audit: `ne_bot_iff`).

`Mathlib/Algebra/Module/Submodule/Lattice.lean`, lines 94–95: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L94-L95

```lean
protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
```

### `Submodule.mem_inf`

Membership in a meet (audit: `mem_inf`).

`Mathlib/Algebra/Module/Submodule/Lattice.lean`, lines 214–216: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L214-L216

```lean
@[simp]
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl
```

### `Submodule.span`

The line `Submodule.span K {fun _ => 1}` of (4), (4′) and (5).

`Mathlib/LinearAlgebra/Span/Defs.lean`, lines 45–47: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean#L45-L47

```lean
/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }
```

### `Submodule.mem_span_singleton`

Membership in the line spanned by one vector (audit: `mem_span_singleton`).

`Mathlib/LinearAlgebra/Span/Defs.lean`, lines 447–457: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean#L447-L457

```lean
theorem mem_span_singleton {y : M} : x ∈ R ∙ y ↔ ∃ a : R, a • y = x :=
  ⟨fun h => by
    refine span_induction ?_ ?_ ?_ ?_ h
    · rintro y (rfl | ⟨⟨_⟩⟩)
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · rintro _ _ - - ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp [add_smul]⟩
    · rintro a _ - ⟨b, rfl⟩
      exact ⟨a * b, by simp [smul_smul]⟩, by
    rintro ⟨a, y, rfl⟩; exact smul_mem _ _ (subset_span <| by simp)⟩
```

## The permutation representation (modeling anchor; not used by the statements)

### `Representation`

Representations as monoid homomorphisms to linear endomorphisms.

`Mathlib/RepresentationTheory/Basic.lean`, lines 47–50: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Basic.lean#L47-L50

```lean
/-- A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V
```

### `Representation.ofMulAction`

The permutation representation on `k[H] = MonoidAlgebra k H`.

`Mathlib/RepresentationTheory/Basic.lean`, lines 395–400: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Basic.lean#L395-L400

```lean
/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def ofMulAction : Representation k G k[H] where
  toFun g := (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
    (coeffLinearEquiv k).toLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]
```

### `MonoidAlgebra`

Its carrier: a one-field structure around the coefficients `M →₀ R`.

`Mathlib/Algebra/MonoidAlgebra/Defs.lean`, lines 71–81: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/MonoidAlgebra/Defs.lean#L71-L81

```lean
/-- The monoid algebra over a semiring `R` generated by the monoid `M`.

It is the type of finite formal `R`-linear combinations of terms of `M`,
endowed with the convolution product. -/
@[to_additive (relevant_arg := M), to_additive_dont_translate]
structure MonoidAlgebra (R M : Type*) [Semiring R] where
  /-- Construct an element of the monoid algebra `R[M]`
  from its coefficients `M →₀ R`. -/
  ofCoeff ::
  /-- The coefficients `M →₀ R` of an element of the monoid algebra `R[M]`. -/
  coeff : M →₀ R
```

### `MonoidAlgebra.coeffLinearEquiv`

`MonoidAlgebra.coeff` as a linear equivalence `S[M] ≃ₗ[R] M →₀ S`.

`Mathlib/Algebra/MonoidAlgebra/Module.lean`, lines 72–75: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/MonoidAlgebra/Module.lean#L72-L75

```lean
/-- `MonoidAlgebra.coeff` as a linear equiv. -/
@[to_additive (attr := simps! apply symm_apply)
/-- `MonoidAlgebra.coeff` as a linear equiv. -/]
def coeffLinearEquiv : S[M] ≃ₗ[R] M →₀ S := coeffAddEquiv.linearEquiv _
```

### `Finsupp.equivFunOnFinite`

`(α →₀ M) ≃ (α → M)` for finite `α`: the passage to `Ω → K`.

`Mathlib/Data/Finsupp/Defs.lean`, lines 204–209: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finsupp/Defs.lean#L204-L209

```lean
/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
```

### `Representation.ofMulAction_single`

Basis vectors go to basis vectors (audit: `ofMulAction_single`).

`Mathlib/RepresentationTheory/Basic.lean`, lines 414–416: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Basic.lean#L414-L416

```lean
@[simp]
theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (single x r) = single (g • x) r := by simp [ofMulAction_def]
```

### `Representation.coeff_ofMulAction`

The action formula `(g • f) x = f (g⁻¹ • x)` on coefficients (audit: `coeff_ofMulAction`).

`Mathlib/RepresentationTheory/Basic.lean`, lines 470–478: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Basic.lean#L470-L478

```lean
@[simp]
theorem coeff_ofMulAction {H : Type*} [MulAction G H] (g : G) (f : k[H]) (h : H) :
    (ofMulAction k G H g f).coeff h = f.coeff (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  set h' := g⁻¹ • h
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp [ofMulAction_def, hg]
```

### `Subrepresentation`

Subrepresentations, in terms of which `IsIrreducible` is defined. The uncompared bridge `BDS/AtomBridge.lean` uses its lattice (below).

`Mathlib/RepresentationTheory/Subrepresentation.lean`, lines 27–34: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Subrepresentation.lean#L27-L34

```lean
/-- A subrepresentation of `G` of the `A`-module `W` is a submodule of `W`
which is stable under the `G`-action.
-/
@[ext]
structure Subrepresentation where
  /-- A subrepresentation is a submodule. -/
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v ∈ toSubmodule → ρ g v ∈ toSubmodule
```

### `Representation.IsIrreducible`

The irreducibility notion that (1) states in unbundled form (the substantive half). The uncompared bridge `BDS/AtomBridge.lean` relates the unbundled form to `IsAtom` in the lattice of subrepresentations instead (below).

`Mathlib/RepresentationTheory/Irreducible.lean`, lines 28–31: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Irreducible.lean#L28-L31

```lean
/-- A representation `ρ` is irreducible if it is non-trivial and has no proper non-trivial
subrepresentations. -/
abbrev IsIrreducible :=
  IsSimpleOrder (Subrepresentation ρ)
```

## The uncompared bridge (`BDS/AtomBridge.lean`; not used by the statements)

`BDS.isAtom_zeroSumSubrep_iff` states that `V₀` is an atom of the lattice of subrepresentations of the permutation representation `BDS.permRep K G Ω` on `Ω → K` if and only if `V₀ ≠ ⊥` and the hypothesis `hirr` holds. It rests on the following, together with `Representation` and `Subrepresentation` above.

### `IsAtom`

Atoms of an order with `⊥`.

`Mathlib/Order/Atoms.lean`, lines 68–71: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Atoms.lean#L68-L71

```lean
/-- An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
```

### `LinearMap.funLeft`

Precomposition as a linear map; `BDS.permRep K G Ω g` is `LinearMap.funLeft K K (g⁻¹ • ·)`, so `(g • f) x = f (g⁻¹ • x)`.

`Mathlib/Algebra/Module/Equiv/Basic.lean`, lines 814–819: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Basic.lean#L814-L819

```lean
/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
```

### `Subrepresentation.instPartialOrder`

The order on subrepresentations (inclusion of carriers), which defines `<` in `IsAtom`.

`Mathlib/RepresentationTheory/Subrepresentation.lean`, lines 52–52: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Subrepresentation.lean#L52-L52

```lean
instance : PartialOrder (Subrepresentation ρ) := .ofSetLike (Subrepresentation ρ) W
```

### `Subrepresentation.instBoundedOrder`

`⊥` and `⊤` of the lattice of subrepresentations; `⊥` has carrier the zero submodule.

`Mathlib/RepresentationTheory/Subrepresentation.lean`, lines 92–96: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RepresentationTheory/Subrepresentation.lean#L92-L96

```lean
instance : BoundedOrder (Subrepresentation ρ) where
  top := ⟨⊤, by simp⟩
  le_top _ := le_top (α := Submodule A W)
  bot := ⟨⊥, by simp⟩
  bot_le _ := bot_le (α := Submodule A W)
```
