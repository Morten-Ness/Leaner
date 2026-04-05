import Mathlib

variable {α : Type*}

variable {α : Type*} [Monoid α]

variable [Preorder α] [CanonicallyOrderedMul α] [MulRightMono α]

theorem Ici_mul_Ici_eq {a b : α} :
    Ici a * Ici b = Ici (a * b) := by
  refine Subset.antisymm (Set.Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in ↦
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
  obtain ⟨d, hd⟩ := exists_mul_of_le <| mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

