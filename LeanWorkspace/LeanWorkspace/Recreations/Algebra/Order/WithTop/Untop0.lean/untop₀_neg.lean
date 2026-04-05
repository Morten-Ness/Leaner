import Mathlib

variable {α : Type*}

theorem untop₀_neg [AddCommGroup α] : ∀ a : WithTop α, (-a).untop₀ = -a.untop₀
  | ⊤ => by simp
  | (a : α) => rfl
