import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by
  simp +contextual only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff, map_zero,
    imp_true_iff]

