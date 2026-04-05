import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem range_id : (AlgHom.id R A).range = ⊤ := SetLike.coe_injective Set.range_id

