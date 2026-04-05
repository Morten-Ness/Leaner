import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := rfl

