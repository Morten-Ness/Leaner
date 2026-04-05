import Mathlib

variable {α : Type*}

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] [MulLeftReflectLE α] [ExistsMulOfLE α]
  {a b c d : α}

theorem smul_Icc (a b c : α) : a • Icc b c = Icc (a * b) (a * c) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    dsimp
    constructor <;> gcongr
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

