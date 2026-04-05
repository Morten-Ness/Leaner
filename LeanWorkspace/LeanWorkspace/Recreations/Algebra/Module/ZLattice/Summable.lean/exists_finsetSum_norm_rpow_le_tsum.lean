import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem exists_finsetSum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-Module.finrank ℤ L : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := by
  classical
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s ↦ ?_⟩
    have hr : r ≠ 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ ↦ by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex ℤ L
  have : Fintype I := inferInstance
  let b : Module.Basis I ℤ L := Module.Free.chooseBasis ℤ L
  simp_rw [Module.finrank_eq_card_basis b]
  set d := Fintype.card I
  have hd : d ≠ 0 := by simp [d]
  let ε := ZLattice.normBound b
  obtain ⟨A, hA, B, hB, H⟩ : ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ r < (-d : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A * B ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
    refine ⟨2 * d * 3 ^ (d - 1), by positivity, ε, ZLattice.normBound_pos b, fun r hr u ↦ ?_⟩
    let e : (I → ℤ) ≃ₗ[ℤ] L := (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).symm
    obtain ⟨u, rfl⟩ : ∃ u' : Finset _, u = u'.image e.toEmbedding :=
      ⟨u.image e.symm.toEmbedding, Finset.coe_injective
        (by simpa using (e.image_symm_image _).symm)⟩
    dsimp
    simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
      Finset.sum_image, ge_iff_le]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ⊆ Fintype.piFinset fun _ : I ↦ Finset.Icc (-n : ℤ) n := by
      obtain ⟨r, hr, hr'⟩ := u.finite_toSet.isCompact.isBounded.subset_closedBall_lt 0 0
      refine ⟨⌊r⌋.toNat, fun x hx ↦ ?_⟩
      have hr'' : ⌊r⌋ ⊔ 0 = ⌊r⌋ := by rw [sup_eq_left]; positivity
      have := hr' hx
      simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le,
        Int.norm_eq_abs, ← Int.cast_abs, ← Int.le_floor] at this
      simpa only [Int.ofNat_toNat, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, hr'']
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn (by intros; positivity)).trans ?_
    dsimp
    simp only [Submodule.norm_coe]
    convert ZLattice.sum_piFinset_Icc_rpow_le b rfl n r hr with x
    simp [e, Finsupp.linearCombination]
  by_cases hA' : A ≤ 1
  · refine ⟨B, hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (by positivity)) hA'
  · refine ⟨A⁻¹ * B, mul_pos (inv_pos.mpr hA) hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [Real.mul_rpow (inv_pos.mpr hA).le hB.le, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) (by positivity))
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hA.le]
    refine Real.self_le_rpow_of_one_le (not_le.mp hA').le ?_
    simp only [neg_mul, one_mul, le_neg (b := r)]
    refine hr.le.trans ?_
    simpa [Nat.one_le_iff_ne_zero]

