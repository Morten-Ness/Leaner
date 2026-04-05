import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem _root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    (S.toSubmodule.toNonUnitalSubalgebra fun _ _ => mul_mem (s := S)) = S :=
  SetLike.coe_injective rfl

