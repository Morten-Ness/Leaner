import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x := Algebra.smul_def' r x

