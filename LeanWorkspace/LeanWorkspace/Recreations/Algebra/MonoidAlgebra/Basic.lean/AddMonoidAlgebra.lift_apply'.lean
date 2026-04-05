import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_apply' (F : Multiplicative M →* A) (f : R[M]) :
    AddMonoidAlgebra.lift R A M F f = f.sum fun a b => algebraMap R A b * F (Multiplicative.ofAdd a) := rfl

