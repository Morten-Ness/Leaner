import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B]

theorem dual_rTensor_conj_homEquiv (f : A →ₗ[R] A') :
    homEquiv.symm.toLinearMap ∘ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _ := rfl

