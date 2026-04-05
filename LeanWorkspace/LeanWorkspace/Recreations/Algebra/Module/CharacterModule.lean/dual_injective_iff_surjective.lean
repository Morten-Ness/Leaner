import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B] {R A' B}

theorem dual_injective_iff_surjective {f : A →ₗ[R] A'} :
    Function.Injective (dual f) ↔ Function.Surjective f := ⟨fun h ↦ CharacterModule.surjective_of_dual_injective f h, fun h ↦ CharacterModule.dual_injective_of_surjective f h⟩

