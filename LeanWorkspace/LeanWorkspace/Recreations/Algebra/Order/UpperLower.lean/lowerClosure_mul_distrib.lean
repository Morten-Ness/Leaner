import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

private theorem one_mul (s : UpperSet α) : 1 * s = s := SetLike.coe_injective <|
    (subset_mul_right _ self_mem_Ici).antisymm' <| by
      rw [← smul_eq_mul, ← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ ↦ s.upper.smul_subset


private theorem one_mul (s : LowerSet α) : 1 * s = s := SetLike.coe_injective <|
    (subset_mul_right _ self_mem_Iic).antisymm' <| by
      rw [← smul_eq_mul, ← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ ↦ s.lower.smul_subset


theorem lowerClosure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerClosure t := SetLike.coe_injective <| by
    rw [LowerSet.coe_mul, mul_lowerClosure, lowerClosure_mul, LowerSet.lowerClosure]

