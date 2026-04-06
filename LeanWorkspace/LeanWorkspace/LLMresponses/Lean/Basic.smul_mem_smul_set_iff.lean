import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := by
      apply smul_left_cancel a
      simpa using hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩
