import Mathlib

variable (ι : Type*)

variable {R : Type*}

variable (A : ι → Type*)

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

theorem algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i ↦ algebraMap R (A i) a := rfl

