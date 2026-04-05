import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem _root_.AlgHom.range_eq_top (f : A →ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f := Algebra.eq_top_iff

