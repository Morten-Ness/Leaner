import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) := smul_mul_assoc r x y

