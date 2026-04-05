import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (A) (f : S →+* R)

theorem compHom_algebraMap_apply (s : S) :
    letI := compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

