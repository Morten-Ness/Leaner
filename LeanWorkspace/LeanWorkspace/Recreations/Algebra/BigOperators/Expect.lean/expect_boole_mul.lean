import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_boole_mul [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (i = j) (Fintype.card ι : M) 0 * f j = f i := by
  simp_rw [Finset.expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [← @NNRat.cast_natCast M, ← NNRat.smul_def, inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

