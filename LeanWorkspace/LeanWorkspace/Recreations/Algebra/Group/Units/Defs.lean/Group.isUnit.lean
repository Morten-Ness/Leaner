import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem Group.isUnit [Group α] (a : α) : IsUnit a := ⟨⟨a, a⁻¹, IsUnit.mul_inv_cancel _, IsUnit.inv_mul_cancel _⟩, rfl⟩

-- namespace

