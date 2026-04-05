import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul).toSubmodule = p := SetLike.coe_injective rfl

