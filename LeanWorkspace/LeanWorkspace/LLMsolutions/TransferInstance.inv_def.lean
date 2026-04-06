import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem inv_def [Group β] (x : α) :
    letI : Group α := Equiv.group e
    x⁻¹ = e.symm ((e x)⁻¹) := by
  rfl
