import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

