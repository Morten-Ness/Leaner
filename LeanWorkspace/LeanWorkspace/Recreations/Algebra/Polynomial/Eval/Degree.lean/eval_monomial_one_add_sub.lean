import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_monomial_one_add_sub [CommRing S] (d : ℕ) (y : S) :
    eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
      ∑ x_1 ∈ range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * y ^ (x_1 - 1)) := by
  have cast_succ : (d + 1 : S) = ((d.succ : ℕ) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ, eval_monomial, eval_monomial, add_comm, add_pow]
  simp only [one_pow, mul_one, mul_comm (y ^ _) (d.choose _)]
  rw [sum_range_succ, mul_add, Nat.choose_self, Nat.cast_one, one_mul, add_sub_cancel_right,
    mul_sum, sum_range_succ', Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun y _hy => ?_
  rw [← mul_assoc, ← mul_assoc, ← Nat.cast_mul, Nat.add_one_mul_choose_eq, Nat.cast_mul,
    Nat.add_sub_cancel]

