import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_eq_fract (m n : E) : ZSpan.fract b m = ZSpan.fract b n ↔ -m + n ∈ span ℤ (Set.range b) := by
  classical
  rw [eq_comm, Module.Basis.ext_elem_iff b]
  simp_rw [ZSpan.repr_fract_apply, Int.fract_eq_fract, eq_comm, Module.Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap ℤ K) _, Set.mem_range]

