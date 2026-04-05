import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (-α) := by
  obtain ⟨e, heα : e ∈ rootSpace H α, he₀ : e ≠ 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  let h : H := ⟨⁅e, f'⁆, hef ▸ Submodule.smul_mem _ _ (Submodule.coe_mem _)⟩
  have hh : α h ≠ 0 := by
    have : h = killingForm K L e f' • (LieAlgebra.IsKilling.cartanEquivDual H).symm α := by
      simp only [h, Subtype.ext_iff, hef]
      rw [Submodule.coe_smul_of_tower]
    rw [this, map_smul, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨hf, LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero hα⟩
  let f := (2 * (α h)⁻¹) • f'
  replace hef : ⁅⁅e, f⁆, e⁆ = 2 • e := by
    have : ⁅⁅e, f'⁆, e⁆ = α h • e := LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace heα h
    rw [lie_smul, smul_lie, this, ← smul_assoc, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hh,
      mul_one, two_smul, two_smul]
  refine ⟨⁅e, f⁆, e, f, ⟨fun contra ↦ ?_, rfl, hef, ?_⟩, heα, Submodule.smul_mem _ _ hfα⟩
  · rw [contra] at hef
    have : IsAddTorsionFree L := .of_isTorsionFree K L
    simp only [zero_lie, eq_comm (a := (0 : L)), smul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hef
    contradiction
  · have : ⁅⁅e, f'⁆, f'⁆ = - α h • f' := LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hfα h
    rw [lie_smul, lie_smul, smul_lie, this]
    simp [← smul_assoc, f, hh, mul_comm _ (2 * (α h)⁻¹)]

