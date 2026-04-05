import Mathlib

variable {α : Type u}

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 := ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

