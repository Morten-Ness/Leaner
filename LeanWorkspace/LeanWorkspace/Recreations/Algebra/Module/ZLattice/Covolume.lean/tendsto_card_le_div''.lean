import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_setOf_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h ↦ hX h (inv_pos_of_pos hc)⟩


theorem tendsto_card_le_div'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nonempty ι] {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' {x | x ∈ X ∧ F x ≤ 1})) = 0) :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}))) := by
  refine Tendsto.congr' ?_ <| (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}) ?_ ?_ h₄ fun x y hx hy ↦ ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x ↦ x ^ (card ι : ℝ)⁻¹) atTop atTop)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    have aux₁ : (card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr card_ne_zero
    have aux₂ : 0 < c ^ (card ι : ℝ)⁻¹ := Real.rpow_pos_of_pos hc _
    have aux₃ : (c ^ (card ι : ℝ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero aux₂.ne'
    have aux₄ : c ^ (-(card ι : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
    rw [Function.comp_apply, ← Real.rpow_natCast, Real.rpow_inv_rpow hc₁ aux₁, eq_comm]
    congr
    refine Nat.card_congr <| Equiv.subtypeEquiv ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.trans
          (Equiv.smulRight aux₄)) fun _ ↦ ?_
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      Equiv.smulRight_apply, Real.rpow_neg hc₁, Set.smul_mem_smul_set_iff₀ aux₃,
      ← Set.mem_smul_set_iff_inv_smul_mem₀ aux₂.ne', ← image_smul_set,
      tendsto_card_le_div''_aux hX h₁ aux₂, ← Real.rpow_natCast, ← Real.rpow_mul hc₁,
      inv_mul_cancel₀ aux₁, Real.rpow_one]
    simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
      and_congr_right_iff, ← b.ofZLatticeBasis_span ℝ, Module.Basis.mem_span_iff_repr_mem,
      Pi.basisFun_repr, Module.Basis.equivFun_apply, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at h₂ ⊢
    exact Bornology.IsVonNBounded.image h₂ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h₃
  · simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX h₁ hx,
      tendsto_card_le_div''_aux hX h₁ (lt_of_lt_of_le hx hy)]
    exact fun a ⟨ha₁, ha₂⟩ ↦ ⟨ha₁, le_trans ha₂ <| pow_le_pow_left₀ (le_of_lt hx) hy _⟩

