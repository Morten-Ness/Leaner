import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂]

variable (f g : M →ₗ[R] M₂)

theorem domRestrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) :
    LinearMap.domRestrict' p f x = f x := rfl

