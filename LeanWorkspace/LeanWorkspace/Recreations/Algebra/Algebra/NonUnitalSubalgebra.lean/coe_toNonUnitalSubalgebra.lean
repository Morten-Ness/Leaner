import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul : Set A) = p := rfl

