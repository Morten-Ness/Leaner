import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_eq_self {x : E} : ZSpan.fract b x = x ↔ x ∈ ZSpan.fundamentalDomain b := by
  classical simp only [Module.Basis.ext_elem_iff b, ZSpan.repr_fract_apply, Int.fract_eq_self,
    ZSpan.mem_fundamentalDomain, Set.mem_Ico]

