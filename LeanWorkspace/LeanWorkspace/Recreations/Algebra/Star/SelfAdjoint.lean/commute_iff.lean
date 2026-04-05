import Mathlib

variable {R A : Type*}

theorem commute_iff {R : Type*} [Mul R] [StarMul R] {x y : R}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdjoint (x * y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [isSelfAdjoint_iff, star_mul, IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy, h.eq]
  · simpa only [star_mul, IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy] using h.symm

