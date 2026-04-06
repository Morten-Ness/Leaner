import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem expect_div (s : Finset ι) (f : ι → M) (a : M) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp only [Finset.expect, div_eq_mul_inv]
  rw [smul_mul_assoc]
  congr 1
  exact Finset.sum_mul ..
