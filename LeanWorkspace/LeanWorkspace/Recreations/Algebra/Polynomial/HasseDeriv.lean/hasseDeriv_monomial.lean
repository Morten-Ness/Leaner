import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_monomial (n : ℕ) (r : R) :
    Polynomial.hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by
  ext i
  simp only [Polynomial.hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · grind
  · rw [if_neg hnik, mul_zero]
    by_cases! hkn : k ≤ n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self]

