import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = LinearMap.mul R A := rfl

