import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

theorem iterate_apply_lie (D : LieDerivation R L L) (n : ℕ) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ ij ∈ antidiagonal n, choose n ij.1 • ⁅D^[ij.1] a, D^[ij.2] b⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅D^[i] a, D^[j] b⁆) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, LieDerivation.apply_lie_eq_add, smul_add,
      sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

