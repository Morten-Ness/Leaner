import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) :
    finrank K (rootSpace H α) = 1 := by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) ≠ 0 := by
      convert_to finrank K (rootSpace H α).toSubmodule ≠ 0
      simpa using α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  let F : rootSpace H α →ₗ[K] K := killingForm K L f ∘ₗ (rootSpace H α).subtype
  have hF : LinearMap.ker F ≠ ⊥ := F.ker_ne_bot_of_finrank_lt <| by rwa [finrank_self]
  obtain ⟨⟨y, hyα⟩, hy, hy₀⟩ := (Submodule.ne_bot_iff _).mp hF
  replace hy : ⁅y, f⁆ = 0 := by
    have : killingForm K L y f = 0 := by simpa [F, traceForm_comm] using hy
    simpa [this] using LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg hyα hfα
  have P : ht.symm.HasPrimitiveVectorWith y (-2 : K) :=
    { ne_zero := by simpa [LieSubmodule.mk_eq_zero] using hy₀
      lie_h := by simp only [neg_smul, neg_lie, ht.h_eq_coroot hα heα hfα,
        ← H.coe_bracket_of_module, LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hyα (LieAlgebra.IsKilling.coroot α),
        LieAlgebra.IsKilling.root_apply_coroot hα]
      lie_e := by rw [← lie_skew, hy, neg_zero] }
  obtain ⟨n, hn⟩ := P.exists_nat
  assumption_mod_cast

