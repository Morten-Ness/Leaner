import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable {S : Type*}

theorem basis_apply (k) [Semiring k] (r : R) :
    MonoidAlgebra.basis R k r = MonoidAlgebra.single r 1 := rfl

