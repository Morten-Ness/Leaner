import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem repr_fract_apply (m : E) (i : ι) : b.repr (ZSpan.fract b m) i = Int.fract (b.repr m i) := by
  rw [ZSpan.fract, map_sub, Finsupp.coe_sub, Pi.sub_apply, ZSpan.repr_floor_apply, Int.fract]

