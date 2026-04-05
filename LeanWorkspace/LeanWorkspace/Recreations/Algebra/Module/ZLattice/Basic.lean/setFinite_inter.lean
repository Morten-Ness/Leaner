import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem setFinite_inter [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ span ℤ (Set.range b)) := by
  have : DiscreteTopology (span ℤ (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

