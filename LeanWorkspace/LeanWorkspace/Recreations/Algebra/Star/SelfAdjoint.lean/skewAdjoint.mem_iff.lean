import Mathlib

variable {R A : Type*}

variable [AddCommGroup R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

