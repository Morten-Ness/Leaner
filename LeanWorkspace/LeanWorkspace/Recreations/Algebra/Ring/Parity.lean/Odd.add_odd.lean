import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.add_odd : Odd a → Odd b → Even (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul, two_mul]
  ac_rfl

