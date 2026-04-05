import Mathlib

variable {ι : Type*} [Fintype ι]

variable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

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


theorem tendsto_card_le_div {X : Set (ι → ℝ)} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : (ι → ℝ) → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x | x ∈ X ∧ F x ≤ 1}) = 0) [Nonempty ι] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set (ι → ℝ)) / (c : ℝ))
        atTop (𝓝 (volume.real {x ∈ X | F x ≤ 1} / ZLattice.covolume L)) := by
  classical
  let e : Free.ChooseBasisIndex ℤ ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis ℤ L).reindex e
  convert ZLattice.covolume.tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [ZLattice.volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  · rw [frontier_equivFun, ZLattice.volume_image_eq_volume_div_covolume, h₄, ENNReal.zero_div]

