import Mathlib

variable {E ι : Type*}

theorem discreteTopology_pi_basisFun [Finite ι] :
    DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage, mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one, Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  refine forall_congr' (fun i => ?_)
  rsuffices ⟨y, hy⟩ : ∃ (y : ℤ), (y : ℝ) = (x : ι → ℝ) i
  · rw [← hy, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, Int.cast_eq_zero]
  exact ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x).mp (SetLike.coe_mem x) i

