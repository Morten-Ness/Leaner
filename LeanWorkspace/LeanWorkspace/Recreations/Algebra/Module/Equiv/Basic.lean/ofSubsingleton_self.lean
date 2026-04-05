import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

theorem ofSubsingleton_self : LinearEquiv.ofSubsingleton M M = refl R M := by
  ext
  simp [eq_iff_true_of_subsingleton]

