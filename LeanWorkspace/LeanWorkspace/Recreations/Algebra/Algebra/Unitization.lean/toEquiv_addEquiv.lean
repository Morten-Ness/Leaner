import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toEquiv_addEquiv [Add R] [Add A] : (Unitization.addEquiv R A).toEquiv = Unitization.equiv := rfl

