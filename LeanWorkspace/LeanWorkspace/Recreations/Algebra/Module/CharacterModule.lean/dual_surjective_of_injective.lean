import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B]

theorem dual_surjective_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective (dual f) := (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

