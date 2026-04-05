import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_fract (m : E) : ZSpan.fract b (ZSpan.fract b m) = ZSpan.fract b m := Module.Basis.ext_elem b fun _ => by classical simp only [ZSpan.repr_fract_apply, Int.fract_fract]

