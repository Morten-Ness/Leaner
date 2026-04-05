import Mathlib

variable {R α β : Type*} [CommSemiring R]

variable (e : α ≃ β)

theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (Equiv.algEquiv R e).symm b = e.symm b := rfl

