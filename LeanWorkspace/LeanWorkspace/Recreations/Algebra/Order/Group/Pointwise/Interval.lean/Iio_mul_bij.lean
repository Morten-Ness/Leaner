import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem Iio_mul_bij : BijOn (· * a) (Iio b) (Iio (b * a)) := Set.image_mul_const_Iio a b ▸ (mul_left_injective _).injOn.bijOn_image

