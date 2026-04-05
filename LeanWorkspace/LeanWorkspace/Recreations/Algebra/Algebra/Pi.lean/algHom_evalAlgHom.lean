import Mathlib

variable (ι : Type*)

variable {R : Type*}

variable (A : ι → Type*)

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

theorem algHom_evalAlgHom : Pi.algHom R A (Pi.evalAlgHom R A) = AlgHom.id R (Π i, A i) := rfl

