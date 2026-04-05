import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_eq_sum_div_card (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, f i = (∑ i ∈ s, f i) / #s := by
  rw [expect, NNRat.smul_def, div_eq_inv_mul, NNRat.cast_inv, NNRat.cast_natCast]

