import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]

