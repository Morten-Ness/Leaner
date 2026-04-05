import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

theorem eq_zero_of_character_apply {a : A} (h : ∀ c : CharacterModule A, c a = 0) : a = 0 := by
  contrapose! h; exact CharacterModule.exists_character_apply_ne_zero_of_ne_zero h

