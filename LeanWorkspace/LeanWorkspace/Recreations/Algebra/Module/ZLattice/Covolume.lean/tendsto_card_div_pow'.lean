import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_setOf_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h ↦ hX h (inv_pos_of_pos hc)⟩


private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Finite ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (b : Module.Basis ι ℝ E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm


theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (volume.real s / ZLattice.covolume L)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert ZLattice.covolume.tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · simp only [measureReal_def]
    rw [ZLattice.volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  · rw [frontier_equivFun, ZLattice.volume_image_eq_volume_div_covolume', hs₃, ENNReal.zero_div]
    exact NullMeasurableSet.of_null hs₃

