import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toAddEquiv_linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
    [Module S R] [Module S A] : (Unitization.linearEquiv S R A).toAddEquiv = Unitization.addEquiv R A := rfl

