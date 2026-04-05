import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_comp (k l : ℕ) :
    (@Polynomial.hasseDeriv R _ k).comp (Polynomial.hasseDeriv l) = (k + l).choose k • Polynomial.hasseDeriv (k + l) := by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, Polynomial.hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases! hikl : i < k + l
  · rw [choose_eq_zero_of_lt hikl, mul_zero]
    by_cases! hil : i < l
    · rw [choose_eq_zero_of_lt hil, mul_zero]
    · rw [← tsub_lt_iff_right hil] at hikl
      rw [choose_eq_zero_of_lt hikl, zero_mul]
  apply @cast_injective ℚ
  have h1 : l ≤ i := le_of_add_le_right hikl
  have h2 : k ≤ i - l := le_tsub_of_add_le_right hikl
  have h3 : k ≤ k + l := le_self_add
  push_cast
  rw [cast_choose ℚ h1, cast_choose ℚ h2, cast_choose ℚ h3, cast_choose ℚ hikl]
  rw [show i - (k + l) = i - l - k by rw [add_comm]; apply tsub_add_eq_tsub_tsub]
  simp only [add_tsub_cancel_left]
  field

