import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_surjective [AddCommMonoid R] [Nonempty n] :
    Function.Surjective (Matrix.trace : Matrix n n R → R) := fun r ↦ by
  classical
  inhabit n
  exact ⟨single default default r, Matrix.trace_single_eq_same default r⟩

