import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B] {R A' B}

set_option backward.isDefEq.respectTransparency false in
theorem surjective_of_dual_injective (f : A →ₗ[R] A') (hf : Function.Injective (dual f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.unique_quotient_iff_eq_top]
  refine ⟨Unique.mk inferInstance fun a ↦ CharacterModule.eq_zero_of_character_apply fun c ↦ ?_⟩
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  suffices eq : dual (Submodule.mkQ _) c = 0 from CharacterModule.congr($eq b)
  refine hf ?_
  rw [← LinearMap.comp_apply, ← CharacterModule.dual_comp, LinearMap.range_mkQ_comp, CharacterModule.dual_zero,
    LinearMap.zero_apply, dual_apply, AddMonoidHom.zero_comp]

