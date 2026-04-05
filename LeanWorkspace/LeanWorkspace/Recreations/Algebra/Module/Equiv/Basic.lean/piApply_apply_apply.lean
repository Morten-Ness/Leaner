import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

theorem piApply_apply_apply {V : M → Type*}
    [CommSemiring R] [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)]
    (e : Π x : M, V x →ₗ[R] R) (s : Π x : M, V x) (x : M) :
    LinearMap.piApply e s x = e x (s x) := rfl

