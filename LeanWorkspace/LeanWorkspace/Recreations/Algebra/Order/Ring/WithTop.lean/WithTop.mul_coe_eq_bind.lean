import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithTop α) = a.bind fun a ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl
