import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ := Algebra.eq_top_iff.2 fun _x => Algebra.mem_top

