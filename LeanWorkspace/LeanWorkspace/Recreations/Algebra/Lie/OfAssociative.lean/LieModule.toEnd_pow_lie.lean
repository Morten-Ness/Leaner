import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieModule.toEnd_pow_lie (x y : L) (z : M) (n : ℕ) :
    ((φ x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((φ x) ^ ij.2) z⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j ↦ ⁅((ad R L x) ^ i) y, ((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_comm, add_left_cancel_iff, Finset.sum_congr rfl]
    rintro ⟨i, j⟩ hij
    rw [mem_antidiagonal] at hij
    rw [Nat.choose_symm_of_eq_add hij.symm]

