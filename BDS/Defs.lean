module
public import Mathlib

@[expose] public section
/-!
# Shared definitions

The definitions on which the compared statements rest. The block between the
`BEGIN`/`END SHARED DEFINITIONS` markers is copied byte for byte into `Challenge.lean`, so the
Challenge imports Mathlib only and elaborates the same declarations, under the same names, as the
proof modules, which are all built on this file.
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
