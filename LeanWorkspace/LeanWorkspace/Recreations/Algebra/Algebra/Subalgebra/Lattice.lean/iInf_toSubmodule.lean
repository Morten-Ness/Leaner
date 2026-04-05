import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iInf_toSubmodule {ι : Sort*} (S : ι → Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) := SetLike.coe_injective <| by simp

