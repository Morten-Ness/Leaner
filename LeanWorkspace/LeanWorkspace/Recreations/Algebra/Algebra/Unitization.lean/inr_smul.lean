import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) := Unitization.ext (smul_zero _).symm rfl

