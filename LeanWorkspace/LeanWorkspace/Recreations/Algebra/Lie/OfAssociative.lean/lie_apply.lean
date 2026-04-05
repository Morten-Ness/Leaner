import Mathlib

variable {A : Type v} [Ring A]

theorem lie_apply {α : Type*} (f g : α → A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ := rfl

