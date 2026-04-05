import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B] {R A' B}

theorem dual_bijective_iff_bijective {f : A →ₗ[R] A'} :
    Function.Bijective (dual f) ↔ Function.Bijective f := ⟨fun h ↦ ⟨CharacterModule.dual_surjective_iff_injective.mp h.2, CharacterModule.dual_injective_iff_surjective.mp h.1⟩,
  fun h ↦ ⟨CharacterModule.dual_injective_iff_surjective.mpr h.2, CharacterModule.dual_surjective_iff_injective.mpr h.1⟩⟩

