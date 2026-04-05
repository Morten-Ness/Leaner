import Mathlib

variable {R α β : Type*} [CommSemiring R]

variable (e : α ≃ β)

theorem algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

