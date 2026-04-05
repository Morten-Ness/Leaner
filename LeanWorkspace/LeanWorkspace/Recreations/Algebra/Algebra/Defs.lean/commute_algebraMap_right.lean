import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem commute_algebraMap_right (r : R) (x : A) : Commute x (algebraMap R A r) := (Algebra.commutes r x).symm

