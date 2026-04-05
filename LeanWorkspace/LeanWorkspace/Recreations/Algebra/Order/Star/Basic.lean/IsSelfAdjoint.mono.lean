import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.mono {x y : R} (h : x ≤ y) (hx : IsSelfAdjoint x) : IsSelfAdjoint y := by
  rw [StarOrderedRing.le_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  rw [IsSelfAdjoint, star_add, hx.star_eq]
  congr
  refine AddMonoidHom.eqOn_closureM (f := starAddEquiv (R := R)) (g := .id R) ?_ hd
  rintro - ⟨s, rfl⟩
  simp

