import Mathlib

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ : L → R)

private theorem aux [h : Nontrivial (LieModule.shiftedGenWeightSpace R L M χ)] : genWeightSpace M χ ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h


theorem exists_nontrivial_weightSpace_of_isNilpotent [Field k] [LieAlgebra k L] [Module k M]
    [Module.Finite k M] [LieModule k L M] [LinearWeights k L M]
    [IsTriangularizable k L M] [Nontrivial M] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace M χ) := by
  obtain ⟨χ⟩ : Nonempty (Weight k L M) := by
    by_contra! contra
    simpa only [iSup_of_empty, bot_ne_top] using LieModule.iSup_genWeightSpace_eq_top' k L M
  obtain ⟨m, hm₀, hm⟩ := LieModule.exists_forall_lie_eq_smul k L M χ
  simp only [LieSubmodule.nontrivial_iff_ne_bot, LieSubmodule.eq_bot_iff, ne_eq, not_forall]
  exact ⟨χ.toLinear, m, by simpa [mem_weightSpace], hm₀⟩

