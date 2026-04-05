import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂]
    [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ / ZLattice.covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
    (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← ZLattice.covolume_comap L₁ volume volume hf, ← ZLattice.covolume_comap L₂ volume volume hf,
    ZLattice.covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'), ZLattice.comap_toAddSubgroup,
    ZLattice.comap_toAddSubgroup, Nat.cast_inj, LinearEquiv.toAddMonoidHom_commutes,
    AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]

