import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r := Algebra.commutes' r x

