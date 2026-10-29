module
public import Mathlib
public import BDS

@[expose] public section
/-!
# Solution

The compared statements of `Challenge.lean`, stated identically (the same opens, namespace,
docstrings and statement text after the shared definitions), each proved by one application of the
theorem of the same name in namespace `BDS`. The definitions they use are those of `BDS.Defs`,
whose text is the shared block of `Challenge.lean`.
-/

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
    W = zeroSum K Ω :=
  BDS.zeroSum_irreducible h2 hcard W hWV hWinv hWne

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
    c = 0 :=
  BDS.additive_core_of_irreducible α hα φ hφ hirr hc0 hcα

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
    c = 0 :=
  BDS.additive_core α hα hcard h2 φ hφ hc0 hcα

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
    c = 0 :=
  BDS.additive_roots_no_relation f hf hdeg h2 hc0 hcα

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
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} :=
  BDS.relModule_le_span_one_of_irreducible α hα htr φ hφ hirr

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
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} :=
  BDS.relModule_le_span_one α hα hcard h2 φ hφ

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
      ≤ Submodule.span K {fun _ => (1 : K)} :=
  BDS.relModule_roots_le_span_one f hf hdeg h2

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
      ∃ t : K, c = fun _ => t :=
  BDS.roots_inhomogeneous_iff_const f hf hdeg h2 c

end DixonRelations
