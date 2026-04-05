import Mathlib

variable {R S : Type*} [Ring R] [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

theorem unitization_range :
    (NonUnitalSubring.unitization s).range = subalgebraOfSubring (.closure s) := by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [NonUnitalSubring.unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_int]

