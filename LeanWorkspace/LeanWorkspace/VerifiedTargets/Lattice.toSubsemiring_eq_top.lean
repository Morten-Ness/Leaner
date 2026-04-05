import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ := Subalgebra.toSubsemiring_injective.eq_iff' Algebra.top_toSubsemiring

