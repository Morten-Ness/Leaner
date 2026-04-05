import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

theorem map_inv_mul {α : Type*} [FunLike F α β] [CommGroup α] [GroupSeminormClass F α β] (x y : α) :
    f (x⁻¹ * y) = f (x * y⁻¹) := by
  rw [← map_inv_eq_map, inv_mul', inv_inv, div_eq_mul_inv]

