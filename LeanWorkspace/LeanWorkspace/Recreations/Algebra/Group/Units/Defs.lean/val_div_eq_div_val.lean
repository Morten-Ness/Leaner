import Mathlib

variable {α : Type u}

variable [DivisionMonoid α]

theorem val_div_eq_div_val : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) := by simp [div_eq_mul_inv]

