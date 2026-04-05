import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : M) 0 * f j = f i := by
  simp_rw [@eq_comm _ _ i, Finset.expect_boole_mul]

