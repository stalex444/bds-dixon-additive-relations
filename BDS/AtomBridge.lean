module
public import Mathlib
public import BDS.AdditiveRelations

@[expose] public section
/-!
# Bridge: the hypothesis `hirr` as an atom of Mathlib's lattice of subrepresentations

Uncompared library material, NOT in `comparator.json`. The hypothesis `hirr` of the compared
criterion forms (2′) and (4′), and the conclusion of the engine (1), are stated for a
`Submodule K (Ω → K)` with an explicit invariance condition. This file relates them to Mathlib's
`Subrepresentation` lattice.

* `BDS.permRep K G Ω` — the permutation representation of `G` on `Ω → K`,
  `(g • f) x = f (g⁻¹ • x)`, built from Mathlib's `LinearMap.funLeft`.
* `BDS.zeroSumSubrep K G Ω` — `V₀ = zeroSum K Ω` as a `Subrepresentation (permRep K G Ω)`.
* `BDS.isAtom_zeroSumSubrep_iff` — `V₀` is an atom of the lattice
  `Subrepresentation (permRep K G Ω)` if and only if `V₀ ≠ ⊥` and `hirr` holds.
* `BDS.isAtom_zeroSumSubrep` — for a finite 2-transitive action with `2 ≤ |Ω|` over a field of
  characteristic 0, `V₀` is such an atom (from the engine (1)).

`permRep` is defined here on `Ω → K`; its transport to Mathlib's `Representation.ofMulAction` on
`K[Ω] = MonoidAlgebra K Ω` is not formalized.
-/

open MulAction
open scoped BigOperators

namespace BDS

section Bridge

variable (K : Type*) [Field K] (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype Ω]

/-- The permutation representation of `G` on `Ω → K`: `(g • f) x = f (g⁻¹ • x)`. -/
def permRep : Representation K G (Ω → K) where
  toFun g := LinearMap.funLeft K K (fun x => g⁻¹ • x)
  map_one' := by
    apply LinearMap.ext; intro f; funext x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    apply LinearMap.ext; intro f; funext x
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_inv_rev, mul_smul]

omit [Fintype Ω] in
lemma permRep_apply (g : G) (f : Ω → K) : permRep K G Ω g f = fun x => f (g⁻¹ • x) := rfl

/-- The zero-sum subspace `V₀ = zeroSum K Ω` as a subrepresentation of `permRep K G Ω`. -/
def zeroSumSubrep : Subrepresentation (permRep K G Ω) where
  toSubmodule := zeroSum K Ω
  apply_mem_toSubmodule g _ hf := zeroSum_invariant g hf

/-- **`hirr` is atomicity of `V₀` in Mathlib's lattice of subrepresentations.** `V₀` is an atom of
`Subrepresentation (permRep K G Ω)` if and only if `V₀ ≠ ⊥` and every nonzero `G`-invariant
`K`-subspace of `V₀` is all of `V₀` (the hypothesis `hirr` of (2′) and (4′)). -/
theorem isAtom_zeroSumSubrep_iff :
    IsAtom (zeroSumSubrep K G Ω) ↔ zeroSum K Ω ≠ ⊥ ∧
      ∀ W : Submodule K (Ω → K), W ≤ zeroSum K Ω →
        (∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W) → W ≠ ⊥ →
          W = zeroSum K Ω := by
  have hbot : ∀ σ : Subrepresentation (permRep K G Ω), σ = ⊥ ↔ σ.toSubmodule = ⊥ := by
    intro σ
    constructor
    · rintro rfl; rfl
    · intro h; exact Subrepresentation.toSubmodule_injective h
  constructor
  · rintro ⟨hne, hlt⟩
    refine ⟨fun h => hne ((hbot _).mpr h), fun W hW hinv hWne => ?_⟩
    let σ : Subrepresentation (permRep K G Ω) := ⟨W, fun g f hf => hinv g f hf⟩
    by_contra hneq
    have hσle : σ ≤ zeroSumSubrep K G Ω := fun x hx => hW hx
    have hσlt : σ < zeroSumSubrep K G Ω :=
      lt_of_le_of_ne hσle (fun h => hneq (congrArg Subrepresentation.toSubmodule h))
    exact hWne ((hbot σ).mp (hlt σ hσlt))
  · rintro ⟨hne, hirr⟩
    refine ⟨fun h => hne ((hbot _).mp h), fun σ hσ => ?_⟩
    rw [hbot]
    by_contra hσne
    have hσle : σ.toSubmodule ≤ zeroSum K Ω := fun x hx => hσ.le hx
    have heq := hirr σ.toSubmodule hσle (fun g f hf => σ.apply_mem_toSubmodule g hf) hσne
    exact hσ.ne (Subrepresentation.toSubmodule_injective heq)

end Bridge

/-- **The engine (1) in atom form.** For a finite group `G` acting 2-transitively on a finite set
`Ω` with `2 ≤ |Ω|`, and a field `K` of characteristic 0, `V₀` is an atom of the lattice of
subrepresentations of the permutation representation `permRep K G Ω`. -/
theorem isAtom_zeroSumSubrep {K : Type*} [Field K] [CharZero K]
    {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) (hcard : 2 ≤ Fintype.card Ω) :
    IsAtom (zeroSumSubrep K G Ω) := by
  rw [isAtom_zeroSumSubrep_iff]
  refine ⟨?_, fun W hWV hWinv hWne => zeroSum_irreducible h2 hcard W hWV hWinv hWne⟩
  have hnt : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  rw [Submodule.ne_bot_iff]
  refine ⟨Pi.single a 1 - Pi.single b 1, ?_, ?_⟩
  · rw [mem_zeroSum]
    simp [Finset.sum_sub_distrib, Finset.sum_pi_single']
  · intro h
    have := congrFun h a
    simp [hab] at this

end BDS
