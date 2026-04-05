import Mathlib

variable {u v : ℤ}

theorem isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  refine ⟨fun h ↦ Int.isUnit_eq_one_or h, fun h ↦ ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

