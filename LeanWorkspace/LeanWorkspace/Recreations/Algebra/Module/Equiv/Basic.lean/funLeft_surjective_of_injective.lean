import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funLeft_surjective_of_injective (f : m → n) (hf : Function.Injective f) :
    Function.Surjective (LinearMap.funLeft R M f) := hf.surjective_comp_right

