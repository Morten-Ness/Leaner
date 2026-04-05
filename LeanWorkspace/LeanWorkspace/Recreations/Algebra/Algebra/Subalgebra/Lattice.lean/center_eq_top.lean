import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ := SetLike.coe_injective (Set.center_eq_univ A)

