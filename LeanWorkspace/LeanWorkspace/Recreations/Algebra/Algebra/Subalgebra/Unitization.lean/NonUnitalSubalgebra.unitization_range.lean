import Mathlib

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

theorem unitization_range : (NonUnitalSubalgebra.unitization s).range = Algebra.adjoin R (s : Set A) := by
  rw [NonUnitalSubalgebra.unitization, Unitization.lift_range]
  simp

