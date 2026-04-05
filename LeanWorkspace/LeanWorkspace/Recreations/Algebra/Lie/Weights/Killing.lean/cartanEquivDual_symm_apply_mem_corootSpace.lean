import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

theorem cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (LieAlgebra.IsKilling.cartanEquivDual H).symm α ∈ corootSpace α := by
  obtain ⟨e : L, he₀ : e ≠ 0, he : ∀ x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e ∈ rootSpace H α := (mem_genWeightSpace L α e).mpr fun x ↦ ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  suffices ⁅e, f⁆ = killingForm K L e f • ((LieAlgebra.IsKilling.cartanEquivDual H).symm α : L) from
    (mem_corootSpace α).mpr <| Submodule.subset_span ⟨(killingForm K L e f)⁻¹ • e,
      Submodule.smul_mem _ _ heα, f, hfα, by simpa [inv_smul_eq_iff₀ hf]⟩
  exact LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα he

