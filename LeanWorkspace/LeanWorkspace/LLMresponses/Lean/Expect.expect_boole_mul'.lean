FAIL
import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : M) 0 * f j = f i := by
  classical
  rw [Finset.expect]
  rw [Finset.smul_sum]
  rw [Finset.sum_eq_single i]
  · simp [smul_eq_mul, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  · intro j _ hj
    simp [hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
