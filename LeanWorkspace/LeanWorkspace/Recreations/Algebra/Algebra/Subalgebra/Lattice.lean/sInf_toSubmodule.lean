import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) := SetLike.coe_injective <| by simp

