import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

theorem Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥ := rfl

