import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] :
    MeasurableSet (ZSpan.fundamentalDomain b) := by
  cases nonempty_fintype ι
  haveI : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let D : Set (ι → ℝ) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : ℝ) 1
  rw [(_ : ZSpan.fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_finiteDimensional _).measurable ?_
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  · ext
    simp only [D, ZSpan.fundamentalDomain, Set.mem_Ico, Set.mem_setOf_eq, LinearEquiv.coe_coe,
      Set.mem_preimage, Module.Basis.equivFun_apply, Set.mem_pi, Set.mem_univ, forall_true_left]

