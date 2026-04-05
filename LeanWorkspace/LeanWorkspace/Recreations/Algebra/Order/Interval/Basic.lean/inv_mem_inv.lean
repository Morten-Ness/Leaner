import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ := ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

