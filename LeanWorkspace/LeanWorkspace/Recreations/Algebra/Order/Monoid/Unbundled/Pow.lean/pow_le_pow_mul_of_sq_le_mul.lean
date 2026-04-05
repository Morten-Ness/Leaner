import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulRightMono M] {x : M}

theorem pow_le_pow_mul_of_sq_le_mul [MulLeftMono M] {a b : M} (hab : a ^ 2 ≤ b * a) :
    ∀ {n}, n ≠ 0 → a ^ n ≤ b ^ (n - 1) * a
  | 1, _ => by simp
  | n + 2, _ => by
    calc
      a ^ (n + 2) = a ^ (n + 1) * a := by rw [pow_succ]
      _ ≤ b ^ n * a * a := by grw [pow_le_pow_mul_of_sq_le_mul hab (by lia)]; simp
      _ = b ^ n * a ^ 2 := by rw [mul_assoc, sq]
      _ ≤ b ^ n * (b * a) := by grw [hab]
      _ = b ^ (n + 1) * a := by rw [← mul_assoc, ← pow_succ]

