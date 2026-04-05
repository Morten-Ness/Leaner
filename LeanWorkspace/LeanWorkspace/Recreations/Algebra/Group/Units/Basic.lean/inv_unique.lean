import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ := Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

