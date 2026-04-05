import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem algebraMap_def {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
    [Algebra R A] [Algebra A α] {S : Subalgebra R A} (s : S) :
  algebraMap S α s = algebraMap A α (s : A) := rfl

