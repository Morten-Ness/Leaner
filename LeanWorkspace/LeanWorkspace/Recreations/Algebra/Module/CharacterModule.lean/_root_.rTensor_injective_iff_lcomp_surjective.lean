import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B] {R A' B}

theorem _root_.rTensor_injective_iff_lcomp_surjective {f : A →ₗ[R] A'} :
    Function.Injective (f.rTensor B) ↔ Function.Surjective (f.lcomp R <| CharacterModule B) := by
  simp [← CharacterModule.dual_rTensor_conj_homEquiv, CharacterModule.dual_surjective_iff_injective]

