import Mathlib

variable {R : Type*}

theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) :
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) ≤ a * b - a / b ^ n := calc
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) =
    (∑ i ∈ range n, a / b ^ (i + 1) * b) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      rw [Nat.sub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, pow_zero,
        Nat.div_one]
    _ ≤ (∑ i ∈ range n, a / b ^ i) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      gcongr with i hi
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _

