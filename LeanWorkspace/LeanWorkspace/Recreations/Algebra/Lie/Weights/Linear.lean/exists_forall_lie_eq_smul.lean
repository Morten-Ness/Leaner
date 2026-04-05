import Mathlib

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ : L → R)

private theorem aux [h : Nontrivial (LieModule.shiftedGenWeightSpace R L M χ)] : genWeightSpace M χ ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h


theorem exists_forall_lie_eq_smul [LinearWeights R L M] [IsNoetherian R M] (χ : Weight R L M) :
    ∃ m : M, m ≠ 0 ∧ ∀ x : L, ⁅x, m⁆ = χ x • m := by
  replace hχ : Nontrivial (LieModule.shiftedGenWeightSpace R L M χ) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr χ.genWeightSpace_ne_bot
  obtain ⟨⟨⟨m, _⟩, hm₁⟩, hm₂⟩ :=
    @exists_ne _ (nontrivial_max_triv_of_isNilpotent R L (LieModule.shiftedGenWeightSpace R L M χ)) 0
  simp_rw [mem_maxTrivSubmodule, Subtype.ext_iff,
    ZeroMemClass.coe_zero] at hm₁
  refine ⟨m, by simpa [LieSubmodule.mk_eq_zero] using hm₂, ?_⟩
  intro x
  have := hm₁ x
  rwa [coe_lie_shiftedGenWeightSpace_apply, sub_eq_zero] at this

