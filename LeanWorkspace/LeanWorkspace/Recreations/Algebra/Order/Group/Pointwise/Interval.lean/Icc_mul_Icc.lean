import Mathlib

variable {α : Type*}

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] [MulLeftReflectLE α] [ExistsMulOfLE α]
  {a b c d : α}

theorem Icc_mul_Icc (hab : a ≤ b) (hcd : c ≤ d) : Icc a b * Icc c d = Icc (a * c) (b * d) := by
  refine (Set.Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ ↦ ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_le_mul_iff_right] at hxbc
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hbcx
    refine ⟨b, right_mem_Icc.2 hab, c * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxbd

