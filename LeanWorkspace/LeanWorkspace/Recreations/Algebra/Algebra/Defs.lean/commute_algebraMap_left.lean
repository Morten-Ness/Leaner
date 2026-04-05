import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem commute_algebraMap_left (r : R) (x : A) : Commute (algebraMap R A r) x := Algebra.commutes r x

