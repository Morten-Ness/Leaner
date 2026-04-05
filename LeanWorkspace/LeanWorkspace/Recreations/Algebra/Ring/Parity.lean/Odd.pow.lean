import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.pow {n : ℕ} (ha : Odd a) : Odd (a ^ n) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha

