import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable (S₁ : NonUnitalSubalgebra R B)

theorem prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule := rfl

