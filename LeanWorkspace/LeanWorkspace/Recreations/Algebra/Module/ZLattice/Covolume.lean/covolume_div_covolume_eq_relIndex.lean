import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ / ZLattice.covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  trans |(b₂.ofZLatticeBasis ℝ).det (b₁.ofZLatticeBasis ℝ)|
  · rw [← Module.Basis.det_mul_det _ (Pi.basisFun ℝ ι) _, abs_mul, Pi.basisFun_det_apply,
      ← Module.Basis.det_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_det_apply,
      ZLattice.covolume_eq_det _ b₁, ZLattice.covolume_eq_det _ b₂, mul_comm, abs_inv]
    congr 3 <;> ext <;> simp
  · rw [Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.ofZLatticeBasis_apply]
    exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (coe_mem _)⟩ i)

