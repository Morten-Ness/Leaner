import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_flip (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    Submodule.map₂ f.flip q p = Submodule.map₂ f p q := by
  rw [Submodule.map₂_eq_span_image2, Submodule.map₂_eq_span_image2, Set.image2_swap]
  rfl

