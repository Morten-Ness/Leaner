import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [Tropical.add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (Tropical.le_zero _) h⟩
    · exact ⟨le_antisymm (Tropical.le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

