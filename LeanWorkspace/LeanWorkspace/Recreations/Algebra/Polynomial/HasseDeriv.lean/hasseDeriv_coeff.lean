import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_coeff (n : ℕ) :
    (Polynomial.hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [Polynomial.hasseDeriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n + k), coeff_monomial]
  · simp
  · #adaptation_note
    /-- Prior to nightly-2025-08-14, this was working as
    `grind [coeff_monomial, Nat.choose_eq_zero_of_lt, Nat.cast_zero, zero_mul]` -/
    intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · grind
  · intro h
    simp only [notMem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]

