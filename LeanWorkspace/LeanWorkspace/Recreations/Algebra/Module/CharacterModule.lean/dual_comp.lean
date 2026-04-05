import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B]

theorem dual_comp {C : Type*} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    dual (g.comp f) = (dual f).comp (dual g) := by
  ext
  rfl

