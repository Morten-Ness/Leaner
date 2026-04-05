import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_span_singleton_eq_map (f : M →ₗ[R] N →ₗ[R] P) (m : M) :
    Submodule.map₂ f (span R {m}) = map (f m) := by
  funext s
  rw [← span_eq s, Submodule.map₂_span_span, image2_singleton_left, map_span]

