import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p := SetLike.coe_injective rfl

