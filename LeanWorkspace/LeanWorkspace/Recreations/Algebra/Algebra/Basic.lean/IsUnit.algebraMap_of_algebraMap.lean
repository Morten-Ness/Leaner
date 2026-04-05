import Mathlib

open scoped Algebra

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem IsUnit.algebraMap_of_algebraMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : IsUnit (algebraMap R A r)) : IsUnit (algebraMap R B r) := let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

