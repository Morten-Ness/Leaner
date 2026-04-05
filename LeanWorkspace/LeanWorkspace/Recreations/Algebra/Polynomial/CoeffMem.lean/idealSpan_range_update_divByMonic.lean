import Mathlib

variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

variable [DecidableEq ι] {i j : ι}

theorem idealSpan_range_update_divByMonic (hij : i ≠ j) (v : ι → R[X]) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by
  rw [modByMonic_eq_sub_mul_div, mul_comm, ← smul_eq_mul, Ideal.span, Ideal.span,
    Submodule.span_range_update_sub_smul hij]

