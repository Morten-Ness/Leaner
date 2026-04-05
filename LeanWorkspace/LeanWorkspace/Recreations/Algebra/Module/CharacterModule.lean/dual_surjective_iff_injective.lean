import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B] {R A' B}

theorem dual_surjective_iff_injective {f : A →ₗ[R] A'} :
    Function.Surjective (dual f) ↔ Function.Injective f := ⟨fun h ↦ (injective_iff_map_eq_zero _).2 fun a h0 ↦ CharacterModule.eq_zero_of_character_apply fun c ↦ by
    obtain ⟨c, rfl⟩ := h c; exact CharacterModule.congr(c $h0).trans c.map_zero,
  CharacterModule.dual_surjective_of_injective f⟩

