import Mathlib

variable (R M : Type u) (M' : Type v) [Semiring R]

theorem cardinalMk_eq_lift_of_fintype [Fintype M'] : #R[M'] = lift.{v} #R ^ card M' := by
  simp [MonoidAlgebra]

