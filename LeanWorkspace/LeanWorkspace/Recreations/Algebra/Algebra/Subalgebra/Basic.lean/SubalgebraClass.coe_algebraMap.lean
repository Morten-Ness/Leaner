import Mathlib

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

theorem coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r := rfl

