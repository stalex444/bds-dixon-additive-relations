module
public import Mathlib
public import BDS.Defs

@[expose] public section
/-!
# Irreducibility of the augmentation module of a 2-transitive action

The representation-theoretic engine cited by Dixon (*Acta Arith.* 82 (1997) 293–302, p. 297) in the
proof of Theorem 1(ii). Dixon cites Curtis & Reiner, *Representation Theory of Finite Groups and
Associative Algebras*, Wiley 1962, §32B; the result is classical (cf. Huppert, *Endliche Gruppen I*,
p. 597, Satz 20.2, as cited by Girstmair, *Acta Arith.* 89 (1999), p. 78). The statement formalized
here:

> If a finite group `G` acts 2-transitively on a finite set `Ω` (with `2 ≤ |Ω|`) and `K` is a field
> of characteristic 0, then the augmentation (zero-sum) subspace `V₀ = {f : Ω → K | ∑ x, f x = 0}`
> of the permutation module `Ω → K` is an irreducible `K[G]`-module.

## Modeling choices (documented)

* The permutation module is the space of functions `Ω → K`. Mathlib's
  `Representation.ofMulAction K G Ω` acts on `K[Ω] = MonoidAlgebra K Ω` instead, which is related to
  `Ω →₀ K` by `MonoidAlgebra.coeffLinearEquiv` and, for a finite `Ω`, to `Ω → K` by
  `Finsupp.equivFunOnFinite`. We take plain functions `Ω → K` so the statement matches the
  classical one with no `Finsupp` bookkeeping.

* The `G`-action is the permutation representation `(g • f) x = f (g⁻¹ • x)`, the formula of
  `Representation.coeff_ofMulAction` read through `MonoidAlgebra.coeffLinearEquiv` and
  `Finsupp.equivFunOnFinite`; the transport of `Representation.ofMulAction` to `Ω → K` is not
  formalized.

* A `G`-subrepresentation is modeled as a `Submodule K (Ω → K)` together with an explicit
  invariance hypothesis `∀ g f, f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W`. This needs no bundled
  `Rep`/`asModule` machinery. The invariance hypothesis is the defining condition of a
  subrepresentation of the permutation representation on `Ω → K` (`BDS.permRep`, in the
  uncompared bridge `BDS/AtomBridge.lean`); its transport to `ofMulAction` on `K[Ω]` is not
  formalized.

* Irreducibility is stated as: every `G`-invariant subspace `W ≤ V₀` is either `⊥` or all of `V₀`.
  Here we prove the substantive half (`W ≠ ⊥ → W = V₀`). Together with the elementary facts, not
  part of this statement, that `V₀` is `G`-invariant and nonzero when `2 ≤ |Ω|`, this is simplicity
  of the `K[G]`-module `V₀`. Over an algebraically closed `K` of characteristic 0 it says that no
  `K`-subspace of `V₀` other than `0` and `V₀` is `G`-invariant, the content of absolute
  irreducibility, stated for `K`-subspaces of `Ω → K`.

* Characteristic 0 is used only to invert the cardinalities `|Stab(a)|` and `|Ω|` in `K`.

The proof is an elementary, character-free stabilizer-averaging argument. Dixon (p. 297) cites
Curtis–Reiner §32B for the statement only; Curtis–Reiner was not consulted, and nothing is claimed
about its proof. The definition `zeroSum` lives in `BDS/Defs.lean` (it is also in the shared block
of `Challenge.lean`); the lemma `mem_zeroSum` is stated below. This file is built on `BDS/Defs.lean`.
-/

open MulAction
open scoped BigOperators

namespace BDS

variable {K : Type*} [Field K] [CharZero K]
variable {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

omit [CharZero K] [DecidableEq Ω] in
@[simp] lemma mem_zeroSum {f : Ω → K} : f ∈ zeroSum K Ω ↔ ∑ x, f x = 0 := Iff.rfl

/-- **Irreducibility of the augmentation module of a 2-transitive action.**

Let a finite group `G` act 2-transitively on a finite set `Ω` with `2 ≤ |Ω|`, and let `K` be a
field of characteristic 0. Then any `G`-invariant `K`-subspace `W` of the permutation module
`Ω → K` that lies inside the zero-sum subspace `V₀` and is nonzero is all of `V₀`. Together with
the elementary facts, not part of this statement, that `V₀` is `G`-invariant and nonzero when
`2 ≤ |Ω|`, this is simplicity of the `K[G]`-module `V₀`. -/
theorem zeroSum_irreducible
    (h2 : IsMultiplyPretransitive G Ω 2)
    (hcard : 2 ≤ Fintype.card Ω)
    (W : Submodule K (Ω → K))
    (hWV : W ≤ zeroSum K Ω)
    (hWinv : ∀ (g : G) (f : Ω → K), f ∈ W → (fun x => f (g⁻¹ • x)) ∈ W)
    (hWne : W ≠ ⊥) :
    W = zeroSum K Ω := by
  classical
  haveI hmp : IsMultiplyPretransitive G Ω 2 := h2
  have hpre : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hWne
  obtain ⟨a, ha⟩ : ∃ a, w a ≠ 0 := by
    rcases Function.ne_iff.mp hw0 with ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  haveI : Nonempty ↥(stabilizer G a) := ⟨1⟩
  have hcardHne : (Fintype.card ↥(stabilizer G a) : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardΩ : (Fintype.card Ω : K) ≠ 0 := by
    have : Fintype.card Ω ≠ 0 := by omega
    exact_mod_cast this
  obtain ⟨wp, hwpW, hwpval⟩ :
      ∃ wp : Ω → K, wp ∈ W ∧ ∀ x, wp x =
        (Fintype.card ↥(stabilizer G a) : K)⁻¹ * ∑ g : ↥(stabilizer G a), w ((g : G)⁻¹ • x) := by
    refine ⟨(Fintype.card ↥(stabilizer G a) : K)⁻¹ •
        ∑ g : ↥(stabilizer G a), (fun x => w ((g : G)⁻¹ • x)), ?_, ?_⟩
    · exact Submodule.smul_mem W _ (Submodule.sum_mem W (fun g _ => hWinv (g : G) w hwW))
    · intro x
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hwpa : wp a = w a := by
    rw [hwpval a]
    have hterm : ∀ g : ↥(stabilizer G a), w ((g : G)⁻¹ • a) = w a := by
      intro g
      congr 1
      exact inv_smul_eq_iff.mpr (mem_stabilizer_iff.mp g.2).symm
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcardHne, one_mul]
  have hwpeq : ∀ x y : Ω, x ≠ a → y ≠ a → wp x = wp y := by
    intro x y hx hy
    obtain ⟨h0, hh0a, hh0xy⟩ := is_two_pretransitive_iff.mp h2 (Ne.symm hx) (Ne.symm hy)
    have hh0mem : h0 ∈ stabilizer G a := mem_stabilizer_iff.mpr hh0a
    rw [hwpval x, hwpval y]
    congr 1
    refine Fintype.sum_bijective (fun g : ↥(stabilizer G a) => (⟨h0, hh0mem⟩ : ↥(stabilizer G a)) * g)
        (Equiv.mulLeft (⟨h0, hh0mem⟩ : ↥(stabilizer G a))).bijective _ _ (fun g => ?_)
    congr 1
    have hcoe : (((⟨h0, hh0mem⟩ : ↥(stabilizer G a)) * g : ↥(stabilizer G a)) : G) = h0 * (g : G) :=
      rfl
    rw [hcoe, mul_inv_rev, mul_smul, ← hh0xy, inv_smul_smul]
  obtain ⟨x0, hx0⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) a
  set c1 : K := wp x0 with hc1def
  have hwpc : ∀ x, x ≠ a → wp x = c1 := fun x hx => by rw [hc1def]; exact hwpeq x x0 hx hx0
  have hne : w a ≠ c1 := by
    intro hcon
    have hconst : ∀ x, wp x = w a := by
      intro x
      by_cases hx : x = a
      · rw [hx, hwpa]
      · rw [hwpc x hx, ← hcon]
    have hsum0 : ∑ x, wp x = 0 := by have := hWV hwpW; rwa [mem_zeroSum] at this
    rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsum0
    rcases mul_eq_zero.mp hsum0 with h | h
    · exact hcardΩ h
    · exact ha h
  have hdiff : ∀ b : Ω, (Pi.single b (1 : K) - Pi.single a (1 : K)) ∈ W := by
    intro b
    by_cases hba : b = a
    · rw [hba, sub_self]; exact Submodule.zero_mem W
    · obtain ⟨g, hg⟩ := hpre.exists_smul_eq a b
      have hga : g⁻¹ • b = a := by rw [inv_smul_eq_iff]; exact hg.symm
      have htW : (fun x => wp (g⁻¹ • x)) ∈ W := hWinv g wp hwpW
      have hval : (fun x => wp (g⁻¹ • x)) - wp
          = (w a - c1) • (Pi.single b (1 : K) - Pi.single a (1 : K)) := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        by_cases hxb : x = b
        · have hxa' : x ≠ a := by rw [hxb]; exact hba
          have hgxa : g⁻¹ • x = a := by rw [hxb]; exact hga
          rw [hgxa, hwpa, hwpc x hxa', if_pos hxb, if_neg hxa']
          ring
        · by_cases hxa : x = a
          · have hgxa : g⁻¹ • x ≠ a := by
              rw [hxa]
              intro h
              have h2 := congrArg (fun z => g • z) h
              rw [smul_inv_smul, hg] at h2
              exact hba h2.symm
            have hwpx : wp x = w a := by rw [hxa]; exact hwpa
            rw [hwpc _ hgxa, hwpx, if_neg hxb, if_pos hxa]
            ring
          · have hgxa : g⁻¹ • x ≠ a := by
              intro h
              apply hxb
              rw [inv_smul_eq_iff] at h
              rw [h]; exact hg
            rw [hwpc _ hgxa, hwpc x hxa, if_neg hxb, if_neg hxa]
            ring
      have hmem : (w a - c1) • (Pi.single b (1 : K) - Pi.single a (1 : K)) ∈ W := by
        rw [← hval]; exact Submodule.sub_mem W htW hwpW
      have hcne : w a - c1 ≠ 0 := sub_ne_zero.mpr hne
      have hfin := Submodule.smul_mem W (w a - c1)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hcne, one_smul] at hfin
  refine le_antisymm hWV ?_
  intro f hf
  rw [mem_zeroSum] at hf
  have hfeq : (∑ x : Ω, f x • (Pi.single x (1 : K) - Pi.single a (1 : K))) = f := by
    have step : (∑ x : Ω, f x • (Pi.single x (1 : K) - Pi.single a (1 : K)))
        = (∑ x : Ω, f x • Pi.single x (1 : K)) - (∑ x : Ω, f x) • Pi.single a (1 : K) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => smul_sub _ _ _)
    rw [step, hf, zero_smul, sub_zero]
    exact (pi_eq_sum_univ' f).symm
  rw [← hfeq]
  exact Submodule.sum_mem W (fun x _ => Submodule.smul_mem W (f x) (hdiff x))

end BDS
