import Mathlib

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

theorem coe_val : (SubalgebraClass.val s : s → A) = ((↑) : s → A) := rfl

