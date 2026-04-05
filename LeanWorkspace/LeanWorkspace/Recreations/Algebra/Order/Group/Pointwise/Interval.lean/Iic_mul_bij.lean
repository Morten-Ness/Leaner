import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem Iic_mul_bij : BijOn (· * a) (Iic b) (Iic (b * a)) := Set.image_mul_const_Iic a b ▸ (mul_left_injective _).injOn.bijOn_image

