import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithTop α) = b.bind fun b ↦ ↑(a * b)
  | ⊤ => by simp [ha]; rfl
  | (b : α) => rfl
