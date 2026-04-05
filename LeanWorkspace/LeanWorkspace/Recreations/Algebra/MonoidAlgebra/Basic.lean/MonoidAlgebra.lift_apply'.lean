import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_apply' (F : M →* A) (f : R[M]) :
    MonoidAlgebra.lift R A M F f = f.sum fun a b => algebraMap R A b * F a := rfl

