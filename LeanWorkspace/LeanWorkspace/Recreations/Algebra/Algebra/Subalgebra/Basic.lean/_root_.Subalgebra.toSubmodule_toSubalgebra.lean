import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S := SetLike.coe_injective rfl

