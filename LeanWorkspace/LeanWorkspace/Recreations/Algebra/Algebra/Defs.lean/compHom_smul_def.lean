import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (A) (f : S →+* R)

theorem compHom_smul_def (s : S) (x : A) :
    letI := compHom A f
    s • x = f s • x := rfl

