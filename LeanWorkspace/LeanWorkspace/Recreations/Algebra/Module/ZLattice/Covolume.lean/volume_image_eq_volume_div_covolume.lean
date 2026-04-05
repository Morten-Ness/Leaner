import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) {s : Set (ι → ℝ)} :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) = volume s / ENNReal.ofReal (ZLattice.covolume L) := by
  rw [LinearEquiv.image_eq_preimage_symm, Measure.addHaar_preimage_linearEquiv,
    LinearEquiv.symm_symm, ZLattice.covolume_eq_det_inv L b, ENNReal.div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

