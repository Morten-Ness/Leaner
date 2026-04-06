FAIL
import Mathlib

variable {R α β : Type*} [CommSemiring R]

variable (e : α ≃ β)

theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI : Semiring α := e.symm.semiring
    letI : Algebra R α := e.symm.toAlgebra
    exact e.symm (e b) = b := by
  exact Equiv.symm_apply_apply e b
