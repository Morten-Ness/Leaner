import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]

