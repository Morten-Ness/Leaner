import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨PreQuasiregular.equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨PreQuasiregular.equiv x, PreQuasiregular.equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply PreQuasiregular.equiv.symm.injective
      assumption

