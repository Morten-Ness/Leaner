import Mathlib

variable {R A : Type*}

theorem charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A := charZero_of_injective_ringHom h

