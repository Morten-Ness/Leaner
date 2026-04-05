import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
  have : a ^ 2 = b ^ 2 := add_right_cancel <|
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul, ← pow_add, add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]

