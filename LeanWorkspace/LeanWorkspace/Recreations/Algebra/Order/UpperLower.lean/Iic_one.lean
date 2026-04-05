import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

private theorem one_mul (s : UpperSet α) : 1 * s = s := SetLike.coe_injective <|
    (subset_mul_right _ self_mem_Ici).antisymm' <| by
      rw [← smul_eq_mul, ← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ ↦ s.upper.smul_subset


omit [IsOrderedMonoid α] in
theorem Iic_one : Iic (1 : α) = 1 := rfl

