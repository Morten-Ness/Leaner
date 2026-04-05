import Mathlib

variable {R S : Type*} [Semiring R] [SetLike S R] [hSR : NonUnitalSubsemiringClass S R] (s : S)

theorem unitization_range :
    (NonUnitalSubsemiring.unitization s).range = subalgebraOfSubsemiring (.closure s) := by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [NonUnitalSubsemiring.unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_nat]

