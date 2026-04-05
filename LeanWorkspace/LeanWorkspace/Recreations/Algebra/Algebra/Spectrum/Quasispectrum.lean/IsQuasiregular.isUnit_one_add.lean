import Mathlib

theorem IsQuasiregular.isUnit_one_add {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) using 1 <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) using 1 <;> [noncomm_ring; simp]

