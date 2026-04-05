import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_add_ZSpan (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    ZSpan.fract b (m + v) = ZSpan.fract b m := by rw [add_comm, ZSpan.fract_zSpan_add b m h]

