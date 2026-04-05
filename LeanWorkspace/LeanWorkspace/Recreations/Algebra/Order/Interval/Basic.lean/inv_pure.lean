import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem inv_pure : (pure a)⁻¹ = pure a⁻¹ := rfl

