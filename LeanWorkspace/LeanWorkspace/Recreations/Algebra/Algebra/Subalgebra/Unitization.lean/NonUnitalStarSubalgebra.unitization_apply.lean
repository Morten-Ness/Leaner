import Mathlib

variable {R S A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

theorem unitization_apply (x : Unitization R s) : NonUnitalStarSubalgebra.unitization s x = algebraMap R A x.fst + x.snd := rfl

