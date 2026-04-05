import Mathlib

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [IsKilling K L] [IsTriangularizable K H L]

private theorem chi_in_q_aux (h_chi_in_q : ↑χ ∈ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have h_h_containment : ⁅x_χ, (y : L)⁆ ∈ genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y ∈ genWeightSpace L (0 : H → K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ ∈
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β ∈ q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H →ₗ[K] K) (hβ_in_q : β_lin ∈ q)
      (hβ_ne_zero : β_lin ≠ 0) : genWeightSpace L β_lin ≤ I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg, this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear ≤ I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy


private theorem chi_not_in_q_aux (h_chi_not_in_q : ↑χ ∉ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : ∃ i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj, Weight.toLinear_neg, ← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj, Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq using 1
      rw [neg_smul, one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_minus_bot
  have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_pos⁆ ∈ (⊥ : LieSubmodule K H L) := by
      rw [← h_plus_bot]
      exact h_pos_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_neg⁆ ∈ (⊥ : LieSubmodule K H L) := by
      rw [← h_minus_bot]
      exact h_neg_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val, hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
        rw [← coe_corootSpace_eq_span_singleton α, LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc, map_smul, h_chi_coroot_zero, smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew, h_lie_eq_smul, h_chi_h_zero, zero_smul, neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum, h_pos_zero, h_neg_zero, h_bracket_zero]
  simp only [add_zero, zero_mem]


include hq hx_χ hαq in
private theorem invtSubmoduleToLieIdeal_aux (hm_α : m_α ∈ sl2SubmoduleOfRoot hα₀) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have hm_α_original : m_α ∈ sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq, ← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp, lie_add, lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ ∈ genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ ∈ genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ, hx_χ_in_H⟩ : H), m_α⁆ = ⁅x_χ, m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ ∈ q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q


theorem lieIdealOrderIso_left_inv (I : LieIdeal K L)
    (hI : ∀ α, I.rootSpan ∈ End.invtSubmodule ((rootSystem H).reflection α).toLinearMap := (rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule) :
    LieAlgebra.IsKilling.invtSubmoduleToLieIdeal I.rootSpan hI = I := by
  set J := LieAlgebra.IsKilling.invtSubmoduleToLieIdeal I.rootSpan
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : ∀ α : H.root, α ∈ J.rootSet ↔ α ∈ I.rootSet := fun α ↦ by
    rw [LieAlgebra.IsKilling.mem_rootSet_invtSubmoduleToLieIdeal, rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h ↦ Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot, I.restr_eq_iSup_sl2SubmoduleOfRoot]
    exact le_antisymm
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj, ← LieSubmodule.restr_toSubmodule J H,
    ← LieSubmodule.restr_toSubmodule I H, h_restr]

