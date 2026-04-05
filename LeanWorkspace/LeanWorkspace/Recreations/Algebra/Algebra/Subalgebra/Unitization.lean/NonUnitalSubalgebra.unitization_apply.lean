import Mathlib

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

theorem unitization_apply (x : Unitization R s) :
    NonUnitalSubalgebra.unitization s x = algebraMap R A x.fst + x.snd := rfl

