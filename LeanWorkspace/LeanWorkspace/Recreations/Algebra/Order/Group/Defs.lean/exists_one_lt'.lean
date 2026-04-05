import Mathlib

variable {α : Type u}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  obtain h | h := hy.lt_or_gt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩

-- see Note [lower instance priority]

