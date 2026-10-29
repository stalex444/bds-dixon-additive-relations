module
public import Mathlib
public import BDS.TwoTransitiveIrreducible

@[expose] public section
/-!
# The additive theorem (no nontrivial zero-sum linear relation among the roots)

This file formalizes the homogeneous case, with coefficients in a field `K` of characteristic 0, of
the additive theorem for 2-transitive Galois groups (Girstmair, *Manuscripta Math.* 39 (1982)
81–97, Proposition 4, Assertion 3, p. 86; Dixon, *Acta Arith.* 82 (1997) 293–302, Theorem 1′,
p. 301), together with its two criterion forms, whose hypothesis is the irreducibility of the
augmentation module instead of 2-transitivity (the 'if' direction of Girstmair 1982,
Proposition 4, Assertion 2, in its module form). It
builds on the representation-theoretic engine `BDS.zeroSum_irreducible` (classical; Dixon p. 297,
citing Curtis–Reiner §32B): the augmentation module of a finite 2-transitive action is an
irreducible `K[G]`-module.

The criterion forms (any field `K`, any group `G`):

* `BDS.additive_core_of_irreducible` — given an injective family `α : Ω → L` into a `K`-vector
  space, a `G`-action on a finite `Ω`, `K`-linear maps `φ g` with `φ g (α x) = α (g • x)`, and the
  hypothesis `hirr` that the zero-sum subspace `V₀` has no `G`-invariant subspace other than `⊥`
  and `V₀`, the only zero-sum `K`-linear relation among the `α x` is trivial.

* `BDS.relModule_le_span_one_of_irreducible` — under the same hypotheses and a transitive action,
  every `K`-linear relation among the `α x` is a scalar multiple of the all-ones tuple.

The 2-transitive forms (characteristic 0, finite `G`), each the engine plus a criterion form:

* `BDS.additive_core` — the abstract core.

* `BDS.relModule_le_span_one` — the span-one form.

* `BDS.additive_roots_no_relation` — the concrete instantiation, in zero-sum form. For an
  irreducible `f : K[X]` of degree `≥ 2` whose Galois group acts 2-transitively on its roots in the
  splitting field, the roots satisfy no nontrivial zero-sum `K`-linear relation.

The definitions `zeroSum`, `relModule` and the lemma `mem_zeroSum` live in `BDS/Defs.lean` and
`BDS/TwoTransitiveIrreducible.lean` (the defs are also in the shared block of `Challenge.lean`);
this file is built on them.
-/

open MulAction
open scoped BigOperators

namespace BDS

/-! ### The criterion forms -/

section Criterion

variable {K : Type*} [Field K]
variable {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
variable {L : Type*} [AddCommGroup L] [Module K L]

@[simp] lemma mem_relModule {α : Ω → L} {c : Ω → K} :
    c ∈ relModule K α ↔ ∑ x, c x • α x = 0 := Iff.rfl

/-- The module of linear relations `relModule K α` is `G`-invariant, in the engine's sense. -/
lemma relModule_invariant (α : Ω → L)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    (g : G) {fn : Ω → K} (h : fn ∈ relModule K α) :
    (fun x => fn (g⁻¹ • x)) ∈ relModule K α := by
  rw [mem_relModule] at h
  show (∑ x, fn (g⁻¹ • x) • α x) = 0
  have hφsum : (∑ x, fn x • α (g • x)) = 0 := by
    have h1 : (φ g) (∑ x, fn x • α x) = (φ g) 0 := by rw [h]
    rw [map_sum, map_zero] at h1
    rw [← h1]
    exact Finset.sum_congr rfl (fun x _ => by rw [map_smul, hφ g x])
  have key : (∑ x, fn x • α (g • x)) = ∑ x, fn (g⁻¹ • x) • α x := by
    have hb := (MulAction.bijective g).sum_comp (fun y => fn (g⁻¹ • y) • α y)
    simp only [inv_smul_smul] at hb
    exact hb
  rw [← key]; exact hφsum

/-- The zero-sum subspace is `G`-invariant: permuting coordinates leaves the sum unchanged. -/
lemma zeroSum_invariant (g : G) {fn : Ω → K} (h : fn ∈ zeroSum K Ω) :
    (fun x => fn (g⁻¹ • x)) ∈ zeroSum K Ω := by
  rw [mem_zeroSum] at h ⊢
  have key : (∑ x, fn (g⁻¹ • x)) = ∑ x, fn x :=
    (MulAction.bijective g⁻¹).sum_comp fn
  rw [key]; exact h

omit [Fintype Ω] in
/-- A vector fixed by a (pre)transitive group action is constant. -/
lemma eq_const_of_invariant {β : Type*} (hpre : IsPretransitive G Ω) {v : Ω → β}
    (hv : ∀ g : G, (fun x => v (g⁻¹ • x)) = v) (a : Ω) : v = fun _ => v a := by
  funext x
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq a x
  have key := congrFun (hv g) x
  have hga : g⁻¹ • x = a := by rw [← hg, inv_smul_smul]
  rw [hga] at key
  exact key.symm

/-- **The additive theorem under the irreducibility criterion (zero-sum form).**

Let a group `G` act on a finite set `Ω`, let `α : Ω → L` be an injective family in a vector space
`L` over a field `K`, and let `φ g : L →ₗ[K] L` (one for each `g`; no homomorphism property is
assumed) satisfy `φ g (α x) = α (g • x)`. Suppose that every nonzero `G`-invariant `K`-subspace of
the zero-sum subspace `V₀ = zeroSum K Ω` is all of `V₀` (`hirr`). Then the family `α` admits no
nontrivial zero-sum `K`-linear relation: any `c : Ω → K` with `∑ x, c x = 0` and
`∑ x, c x • α x = 0` is `0`. -/
theorem additive_core_of_irreducible
    (α : Ω → L) (hα : Function.Injective α)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    (hirr : ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
      (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ → W = zeroSum K Ω)
    {c : Ω → K} (hc0 : ∑ x, c x = 0) (hcα : ∑ x, c x • α x = 0) :
    c = 0 := by
  classical
  -- `G`-invariance of `W := relModule K α ⊓ zeroSum K Ω` in the engine's sense.
  have hWinv : ∀ (g : G) (fn : Ω → K), fn ∈ relModule K α ⊓ zeroSum K Ω →
      (fun x => fn (g⁻¹ • x)) ∈ relModule K α ⊓ zeroSum K Ω := by
    intro g fn hfn
    rw [Submodule.mem_inf] at hfn ⊢
    exact ⟨relModule_invariant α φ hφ g hfn.1, zeroSum_invariant g hfn.2⟩
  -- Apply the criterion: `W` is either `⊥` or all of `zeroSum K Ω`.
  by_cases hbot : relModule K α ⊓ zeroSum K Ω = ⊥
  · have hcmem : c ∈ relModule K α ⊓ zeroSum K Ω :=
      Submodule.mem_inf.mpr ⟨by rw [mem_relModule]; exact hcα, by rw [mem_zeroSum]; exact hc0⟩
    rw [hbot, Submodule.mem_bot] at hcmem
    exact hcmem
  · exfalso
    have hWeq : relModule K α ⊓ zeroSum K Ω = zeroSum K Ω := hirr _ inf_le_right hWinv hbot
    -- A nonzero zero-sum vector needs two distinct points.
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hnt : Nontrivial Ω := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      apply hw0
      have hz : ∑ x, w x = 0 := (Submodule.mem_inf.mp hwW).2
      funext y
      rw [Fintype.sum_subsingleton w y] at hz
      exact hz
    obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
    -- `e_a - e_b` lies in `zeroSum K Ω = W`, hence in `relModule K α`, forcing `α a = α b`.
    have s1 : (∑ x, (Pi.single a 1 : Ω → K) x) = 1 := by
      rw [Finset.sum_eq_single_of_mem (f := fun x => (Pi.single a 1 : Ω → K) x) a
        (Finset.mem_univ a) (fun x _ hx => by simp [hx])]
      simp
    have s2 : (∑ x, (Pi.single b 1 : Ω → K) x) = 1 := by
      rw [Finset.sum_eq_single_of_mem (f := fun x => (Pi.single b 1 : Ω → K) x) b
        (Finset.mem_univ b) (fun x _ hx => by simp [hx])]
      simp
    have hzs : (Pi.single a 1 - Pi.single b 1 : Ω → K) ∈ zeroSum K Ω := by
      rw [mem_zeroSum]
      have expand : (∑ x, (Pi.single a 1 - Pi.single b 1 : Ω → K) x)
          = (∑ x, (Pi.single a 1 : Ω → K) x) - (∑ x, (Pi.single b 1 : Ω → K) x) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [Pi.sub_apply])
      rw [expand, s1, s2, sub_self]
    rw [← hWeq, Submodule.mem_inf] at hzs
    have hvU := hzs.1
    rw [mem_relModule] at hvU
    have e1 : (∑ x, (Pi.single a 1 : Ω → K) x • α x) = α a := by
      rw [Finset.sum_eq_single_of_mem (f := fun x => (Pi.single a 1 : Ω → K) x • α x) a
        (Finset.mem_univ a) (fun x _ hx => by simp [hx])]
      simp
    have e2 : (∑ x, (Pi.single b 1 : Ω → K) x • α x) = α b := by
      rw [Finset.sum_eq_single_of_mem (f := fun x => (Pi.single b 1 : Ω → K) x • α x) b
        (Finset.mem_univ b) (fun x _ hx => by simp [hx])]
      simp
    have hval : (∑ x, (Pi.single a 1 - Pi.single b 1 : Ω → K) x • α x) = α a - α b := by
      have expand : (∑ x, (Pi.single a 1 - Pi.single b 1 : Ω → K) x • α x)
          = (∑ x, (Pi.single a 1 : Ω → K) x • α x) - (∑ x, (Pi.single b 1 : Ω → K) x • α x) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [Pi.sub_apply, sub_smul])
      rw [expand, e1, e2]
    rw [hval] at hvU
    exact hab (hα (sub_eq_zero.mp hvU))

/-- **The additive theorem under the irreducibility criterion (span-one form).**

Under the hypotheses of `additive_core_of_irreducible`, and if `G` acts transitively on `Ω`, every
`K`-linear relation among the family `α` is a scalar multiple of the all-ones tuple:
`relModule K α` is contained in the line spanned by the constant tuple `1`. No averaging is used,
so `K` is any field. -/
theorem relModule_le_span_one_of_irreducible
    (α : Ω → L) (hα : Function.Injective α)
    (htr : IsPretransitive G Ω)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    (hirr : ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
      (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ → W = zeroSum K Ω) :
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} := by
  intro c hc
  -- Each translate of `c` is a relation with the same coefficient sum, so the difference is a
  -- zero-sum relation, hence `0`: `c` is `G`-invariant.
  have hinv : ∀ g : G, (fun x => c (g⁻¹ • x)) = c := by
    intro g
    have hs : (∑ x, c (g⁻¹ • x)) = ∑ x, c x := (MulAction.bijective g⁻¹).sum_comp c
    have hcg : (∑ x, c (g⁻¹ • x) • α x) = 0 :=
      mem_relModule.mp (relModule_invariant α φ hφ g hc)
    have hd : c - (fun x => c (g⁻¹ • x)) = 0 := by
      apply additive_core_of_irreducible α hα φ hφ hirr
      · simp only [Pi.sub_apply]
        rw [Finset.sum_sub_distrib, hs, sub_self]
      · simp only [Pi.sub_apply, sub_smul]
        rw [Finset.sum_sub_distrib, mem_relModule.mp hc, hcg, sub_zero]
    exact (sub_eq_zero.mp hd).symm
  -- A `G`-invariant tuple over a transitive action is constant.
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨a⟩⟩
  · have hc0 : c = 0 := funext (fun x => isEmptyElim x)
    rw [hc0]; exact Submodule.zero_mem _
  · rw [eq_const_of_invariant htr hinv a]
    exact Submodule.mem_span_singleton.mpr ⟨c a, by funext x; simp⟩

end Criterion

/-! ### The 2-transitive forms -/

section TwoTransitive

variable {K : Type*} [Field K] [CharZero K]
variable {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
variable {L : Type*} [AddCommGroup L] [Module K L]

/-- **Abstract additive theorem, zero-sum form** (Dixon, Theorem 1′, homogeneous case, zero-sum
part, for an abstract family).

Let a finite group `G` act 2-transitively on a finite set `Ω` with `2 ≤ |Ω|`, let `K` be a field of
characteristic 0, let `α : Ω → L` be an injective family in a `K`-vector space `L`, and let
`φ g : L →ₗ[K] L` satisfy `φ g (α x) = α (g • x)`. Then the family `α` admits no nontrivial
zero-sum `K`-linear relation: any `c : Ω → K` with `∑ x, c x = 0` and `∑ x, c x • α x = 0` is `0`.
This is `additive_core_of_irreducible` with its hypothesis `hirr` supplied by the engine
`zeroSum_irreducible`. -/
theorem additive_core
    (α : Ω → L) (hα : Function.Injective α)
    (hcard : 2 ≤ Fintype.card Ω)
    (h2 : IsMultiplyPretransitive G Ω 2)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x))
    {c : Ω → K} (hc0 : ∑ x, c x = 0) (hcα : ∑ x, c x • α x = 0) :
    c = 0 :=
  additive_core_of_irreducible α hα φ hφ
    (fun W hWV hWinv hWne => zeroSum_irreducible h2 hcard W hWV hWinv hWne) hc0 hcα

/-- **The relation module lies in the span of the all-ones tuple.** Under the hypotheses of
`additive_core`, every `K`-linear relation among the family `α` is a scalar multiple of the
all-ones tuple: `relModule K α` is contained in the line spanned by the constant tuple `1`. This is
`relModule_le_span_one_of_irreducible` with `hirr` supplied by the engine `zeroSum_irreducible`
and transitivity by `isPretransitive_of_is_two_pretransitive`. -/
theorem relModule_le_span_one
    (α : Ω → L) (hα : Function.Injective α)
    (hcard : 2 ≤ Fintype.card Ω)
    (h2 : IsMultiplyPretransitive G Ω 2)
    (φ : G → (L →ₗ[K] L)) (hφ : ∀ (g : G) (x : Ω), φ g (α x) = α (g • x)) :
    relModule K α ≤ Submodule.span K {fun _ : Ω => (1 : K)} :=
  relModule_le_span_one_of_irreducible α hα (isPretransitive_of_is_two_pretransitive (h2 := h2))
    φ hφ (fun W hWV hWinv hWne => zeroSum_irreducible h2 hcard W hWV hWinv hWne)

end TwoTransitive

/-! ### Concrete instantiation: roots of an irreducible polynomial, characteristic 0 -/

open Polynomial in
/-- **The additive theorem at the roots of an irreducible polynomial, zero-sum form** (Dixon,
Theorem 1′, homogeneous case, zero-sum part; over a field `K` of characteristic 0). The full
homogeneous case at the roots is `BDS.relModule_roots_le_span_one`, and the case of relations with
value in `K` is `BDS.roots_inhomogeneous_iff_const` (both in `BDS/RootsCorollaries.lean`).

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
  classical
  have hsep : f.Separable := hf.separable
  have hsplit : (f.map (algebraMap K f.SplittingField)).Splits :=
    Polynomial.SplittingField.splits f
  have hcard : 2 ≤ Fintype.card (f.rootSet f.SplittingField) := by
    rw [card_rootSet_eq_natDegree hsep hsplit]; exact hdeg
  refine additive_core (G := f.Gal) (Ω := f.rootSet f.SplittingField)
    (Subtype.val) Subtype.val_injective hcard h2
    (fun g => (g : f.SplittingField ≃ₐ[K] f.SplittingField).toLinearMap) ?_ hc0 hcα
  intro g r
  rfl

end BDS
