import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

theorem exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a ≠ 0) :
    ∃ (c : CharacterModule A), c a ≠ 0 := have ⟨c, hc⟩ := CharacterModule.dual_surjective_of_injective _ (Submodule.injective_subtype _) (CharacterModule.ofSpanSingleton a)
  ⟨c, fun h ↦ ne_zero <| CharacterModule.eq_zero_of_ofSpanSingleton_apply_self a <| by rwa [← hc]⟩

