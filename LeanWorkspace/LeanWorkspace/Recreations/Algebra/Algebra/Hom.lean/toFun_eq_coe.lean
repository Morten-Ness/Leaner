import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f := rfl

