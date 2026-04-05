import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range := SetLike.coe_injective Set.image_univ

