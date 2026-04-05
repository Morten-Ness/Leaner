import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem _root_.toAlgebra_algebraMap [Algebra R S] :
    (algebraMap R S).toAlgebra = ‹_› := Algebra.algebra_ext _ _ fun _ ↦ rfl

-- see Note [lower instance priority]

