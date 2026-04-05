import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

set_option backward.isDefEq.respectTransparency false in
theorem summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r := by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (ZLattice.summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  refine ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * ‖x‖)) H).preimage_embedding
    (.subtype _)).subset ?_
  intro t ht
  by_cases ht₁ : ‖t‖ = 0
  · simp [show t = 0 by simpa using ht₁]
  by_cases ht₂ : ‖t - x‖ = 0
  · simpa [show t = x by simpa [sub_eq_zero] using ht₂, two_mul] using t.2
  have : 0 < Module.finrank ℤ L := Module.finrank_pos
  have : ‖t - x‖ < 2⁻¹ * ‖t‖ := by
    rw [← Real.rpow_lt_rpow_iff_of_neg (by positivity) (by positivity) (hr.trans (by simpa))]
    simpa [Real.mul_rpow, abs_eq_self.mpr (show 0 ≤ ‖t - x‖ ^ r by positivity)] using ht
  have := (norm_sub_norm_le _ _).trans_lt this
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', AddSubgroupClass.coe_norm] at this
  simpa using show ‖t.1‖ ≤ 2 * ‖x‖ by linarith

