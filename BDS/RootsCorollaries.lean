module
public import Mathlib
public import BDS.AdditiveRelations

@[expose] public section
/-!
# The additive theorem at the roots: span-one form and relations with value in `K`

The library proofs of compared statements (5) and (6) (`comparator.json`; `Solution.lean` applies
`BDS.relModule_roots_le_span_one` and `BDS.roots_inhomogeneous_iff_const`). Both concern a field
`K` of characteristic 0 and an irreducible `f : K[X]` of degree `≥ 2` whose Galois group acts
2-transitively on the roots of `f` in the splitting field (the hypotheses of compared statement
(3)).

* `BDS.exists_sum_rootSet_eq_algebraMap` — for any field `K` and any separable `f : K[X]`, the sum
  of the roots of `f` in the splitting field lies in `K`. The splitting field of a separable
  polynomial is Galois over `K`, and the sum of the roots is fixed by every automorphism, which
  permutes the roots. No characteristic, irreducibility or transitivity hypothesis.
* `BDS.relModule_roots_le_span_one` — compared statement (5): compared statement (4) instantiated
  at the roots, by the same instantiation as (3): every `K`-linear relation `∑ r, c r • r = 0`
  among the roots has `c` constant.
* `BDS.roots_inhomogeneous_const` — the relations with value in `K`: if
  `∑ r, c r • r = algebraMap K f.SplittingField k` for some `k : K`, then `c` is constant. This is
  the forward direction of compared statement (6). The proof: each Galois translate of `c` has the
  same value `k` and the same coefficient sum, so the difference is a zero-sum relation, hence `0`
  by `BDS.additive_core`; a Galois-invariant tuple on a transitive root set is constant.
* `BDS.roots_inhomogeneous_iff_const` — compared statement (6): a coefficient tuple `c` satisfies
  `∑ r, c r • r = algebraMap K f.SplittingField k` for some `k : K` if and only if `c` is
  constant. This is Dixon's Theorem 1′ (Acta Arith. 82 (1997), p. 301), `U = K·e`, for relations
  with value in `K` (`∑ c_α α ∈ K`), for every field `K` of characteristic 0, with the roots in
  Mathlib's `f.SplittingField`. The forward direction is `BDS.roots_inhomogeneous_const`; the
  reverse direction is `BDS.exists_sum_rootSet_eq_algebraMap`, with separability from
  `Irreducible.separable` (characteristic 0).
-/

open MulAction Polynomial
open scoped BigOperators

namespace BDS

/-- **The sum of the roots lies in the base field.** For any field `K` and any separable
`f : K[X]`, the sum of the roots of `f` in its splitting field is the image of an element of `K`.
The splitting field of a separable polynomial is Galois over `K`, and every automorphism permutes
the roots, so it fixes their sum. -/
theorem exists_sum_rootSet_eq_algebraMap {K : Type*} [Field K] (f : K[X]) (hf : f.Separable) :
    ∃ k : K, ∑ r : f.rootSet f.SplittingField, (r : f.SplittingField)
      = algebraMap K f.SplittingField k := by
  classical
  have : IsGalois K f.SplittingField := IsGalois.of_separable_splitting_field hf
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K)
    (∑ r : f.rootSet f.SplittingField, (r : f.SplittingField))).mpr (by
      intro σ
      let g : f.Gal := σ
      rw [map_sum]
      exact (MulAction.bijective g).sum_comp
        (fun y : f.rootSet f.SplittingField => (y : f.SplittingField)))
  exact ⟨k, hk.symm⟩

variable {K : Type*} [Field K] [CharZero K]

/-- **Compared statement (4) at the roots (compared statement (5)).** For a field `K` of
characteristic 0 and an irreducible `f : K[X]` of degree `≥ 2` whose Galois group acts
2-transitively on the roots in the splitting field, every `K`-linear relation among the roots is a
scalar multiple of the all-ones tuple. -/
theorem relModule_roots_le_span_one (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2) :
    relModule K (fun r : f.rootSet f.SplittingField => (r : f.SplittingField))
      ≤ Submodule.span K {fun _ => (1 : K)} := by
  classical
  have hcard : 2 ≤ Fintype.card (f.rootSet f.SplittingField) := by
    rw [card_rootSet_eq_natDegree hf.separable (SplittingField.splits f)]; exact hdeg
  exact BDS.relModule_le_span_one (G := f.Gal) Subtype.val Subtype.val_injective hcard h2
    (fun g => (g : f.SplittingField ≃ₐ[K] f.SplittingField).toLinearMap) (fun _ _ => rfl)

/-- **Relations with value in `K` at the roots (forward direction of compared statement (6)).**
For a field `K` of
characteristic 0 and an irreducible `f : K[X]` of degree `≥ 2` whose Galois group acts
2-transitively on the roots in the splitting field, if `∑ r, c r • r = k` for some `k : K`, then
`c` is constant. -/
theorem roots_inhomogeneous_const (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2)
    (c : f.rootSet f.SplittingField → K) (k : K)
    (hck : ∑ r, c r • (r : f.SplittingField) = algebraMap K f.SplittingField k) :
    ∃ t : K, c = fun _ => t := by
  classical
  have hcard : 2 ≤ Fintype.card (f.rootSet f.SplittingField) := by
    rw [card_rootSet_eq_natDegree hf.separable (SplittingField.splits f)]; exact hdeg
  have hpre : IsPretransitive f.Gal (f.rootSet f.SplittingField) :=
    isPretransitive_of_is_two_pretransitive (h2 := h2)
  -- each translate of `c` has the same value `k`
  have htrans : ∀ g : f.Gal, ∑ x : f.rootSet f.SplittingField, c (g⁻¹ • x) • (x : f.SplittingField)
      = algebraMap K f.SplittingField k := by
    intro g
    have h1 : (∑ x : f.rootSet f.SplittingField,
        c x • ((g • x : f.rootSet f.SplittingField) : f.SplittingField)) = algebraMap K _ k := by
      have : (∑ x : f.rootSet f.SplittingField,
          c x • ((g • x : f.rootSet f.SplittingField) : f.SplittingField))
          = (g : f.SplittingField ≃ₐ[K] f.SplittingField).toLinearMap
              (∑ x : f.rootSet f.SplittingField, c x • (x : f.SplittingField)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun x _ => by rw [map_smul]; rfl)
      rw [this, hck]; exact AlgEquiv.commutes _ k
    rw [← h1]
    have hb := (MulAction.bijective g).sum_comp
      (fun y : f.rootSet f.SplittingField => c (g⁻¹ • y) • (y : f.SplittingField))
    simp only [inv_smul_smul] at hb
    exact hb.symm
  -- so `c` is Galois-invariant: the difference with a translate is a zero-sum relation
  have hinv : ∀ g : f.Gal, (fun x => c (g⁻¹ • x)) = c := by
    intro g
    have hs : (∑ x : f.rootSet f.SplittingField, c (g⁻¹ • x))
        = ∑ x : f.rootSet f.SplittingField, c x := (MulAction.bijective g⁻¹).sum_comp c
    have hd : c - (fun x => c (g⁻¹ • x)) = 0 := by
      apply BDS.additive_core (G := f.Gal) Subtype.val Subtype.val_injective hcard h2
        (fun g => (g : f.SplittingField ≃ₐ[K] f.SplittingField).toLinearMap) (fun _ _ => rfl)
      · simp only [Pi.sub_apply]; rw [Finset.sum_sub_distrib, hs, sub_self]
      · simp only [Pi.sub_apply, sub_smul]; rw [Finset.sum_sub_distrib, hck, htrans g, sub_self]
    exact (sub_eq_zero.mp hd).symm
  obtain ⟨a⟩ : Nonempty (f.rootSet f.SplittingField) := Fintype.card_pos_iff.mp (by omega)
  exact ⟨c a, BDS.eq_const_of_invariant hpre hinv a⟩

/-- **Relations with value in `K` at the roots: Dixon's `U = K·e` (compared statement (6)).** For a
field `K` of characteristic 0 and an irreducible `f : K[X]` of degree `≥ 2` whose Galois group acts
2-transitively on the roots in the splitting field, a coefficient tuple `c` satisfies
`∑ r, c r • r = k` for some `k : K` if and only if `c` is constant. -/
theorem roots_inhomogeneous_iff_const (f : K[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (h2 : IsMultiplyPretransitive f.Gal (f.rootSet f.SplittingField) 2)
    (c : f.rootSet f.SplittingField → K) :
    (∃ k : K, ∑ r, c r • (r : f.SplittingField) = algebraMap K f.SplittingField k) ↔
      ∃ t : K, c = fun _ => t := by
  constructor
  · rintro ⟨k, hk⟩
    exact roots_inhomogeneous_const f hf hdeg h2 c k hk
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := exists_sum_rootSet_eq_algebraMap f hf.separable
    refine ⟨t * s, ?_⟩
    calc ∑ r : f.rootSet f.SplittingField, (fun _ => t) r • (r : f.SplittingField)
        = t • ∑ r : f.rootSet f.SplittingField, (r : f.SplittingField) := by
          rw [Finset.smul_sum]
      _ = algebraMap K f.SplittingField (t * s) := by
          rw [hs, Algebra.smul_def, map_mul]

end BDS
