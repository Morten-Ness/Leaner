import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem abs_sub_map_le_div [Group α] [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupSeminormClass F α β]
    (f : F) (x y : α) : |f x - f y| ≤ f (x / y) := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩

-- See note [lower instance priority]

