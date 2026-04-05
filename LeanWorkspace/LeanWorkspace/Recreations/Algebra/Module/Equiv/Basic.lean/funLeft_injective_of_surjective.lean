import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funLeft_injective_of_surjective (f : m → n) (hf : Function.Surjective f) :
    Function.Injective (LinearMap.funLeft R M f) := hf.injective_comp_right

