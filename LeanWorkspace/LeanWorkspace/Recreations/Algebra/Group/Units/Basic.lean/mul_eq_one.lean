import Mathlib

variable {α : Type u}

variable [CommMonoid α]

variable [Subsingleton αˣ] {a b : α}

theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 := ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

