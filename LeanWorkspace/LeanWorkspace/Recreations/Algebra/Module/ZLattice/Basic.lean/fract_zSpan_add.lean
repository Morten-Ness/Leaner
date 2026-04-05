import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_zSpan_add (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    ZSpan.fract b (v + m) = ZSpan.fract b m := by
  classical
  refine (Module.Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [ZSpan.repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars ℤ).repr ⟨v, h⟩ i
  rw [map_add, Finsupp.coe_add, Pi.add_apply, add_tsub_cancel_right,
    ← eq_intCast (algebraMap ℤ K) _, Module.Basis.restrictScalars_repr_apply, coe_mk]

