import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa using hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa using hg⟩
