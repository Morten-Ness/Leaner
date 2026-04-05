import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  constructor
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro x hx hx'
    apply h
    · exact Set.smul_mem_smul_set hx
    · rcases hx' with ⟨y, hy, rfl⟩
      simpa [smul_smul]
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro x hx hx'
    rcases hx with ⟨y, hy, rfl⟩
    apply h hy
    refine ⟨a • y, hx', ?_⟩
    simp [smul_smul]
