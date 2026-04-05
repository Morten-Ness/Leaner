import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_add_C_pow (r : R) (n k : ℕ) :
    ((Polynomial.X + Polynomial.C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  rw [(commute_X (Polynomial.C r : R[X])).add_pow, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, ← C_eq_natCast, ← C_pow, Polynomial.coeff_mul_C]
  rw [Finset.sum_eq_single k, Polynomial.coeff_X_pow_self, one_mul]
  · intro _ _ h
    simp [Polynomial.coeff_X_pow, h.symm]
  · simp only [Polynomial.coeff_X_pow_self, one_mul, not_lt, Finset.mem_range]
    intro h
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

