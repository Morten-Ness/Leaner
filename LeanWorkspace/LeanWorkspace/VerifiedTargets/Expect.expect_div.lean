import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_div (s : Finset ι) (f : ι → M) (a : M) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, Finset.expect_mul]

