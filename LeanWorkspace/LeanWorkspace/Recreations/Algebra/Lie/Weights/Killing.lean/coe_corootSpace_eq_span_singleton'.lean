import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [PerfectField K]

theorem coe_corootSpace_eq_span_singleton' (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ (LieAlgebra.IsKilling.cartanEquivDual H).symm α := by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} ⊆
        K ∙ ((LieAlgebra.IsKilling.cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      exact ⟨killingForm K L e f, rfl⟩
    simp only [LieSubmodule.mem_toSubmodule, mem_corootSpace] at hx'
    replace this := Submodule.span_mono this hx'
    rw [Submodule.span_span] at this
    rw [Submodule.mem_span_singleton] at this ⊢
    obtain ⟨t, rfl⟩ := this
    solve_by_elim
  · simp only [Submodule.span_singleton_le_iff_mem, LieSubmodule.mem_toSubmodule]
    exact LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace α

