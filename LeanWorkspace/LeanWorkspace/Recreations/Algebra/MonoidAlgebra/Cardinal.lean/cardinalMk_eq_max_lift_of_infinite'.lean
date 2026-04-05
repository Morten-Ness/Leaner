import Mathlib

variable (R M : Type u) (M' : Type v) [Semiring R]

theorem cardinalMk_eq_max_lift_of_infinite' [Nonempty M'] [Infinite R] :
    #R[M'] = max (lift.{v} #R) (lift.{u} #M') := by simp [MonoidAlgebra, max_comm]

