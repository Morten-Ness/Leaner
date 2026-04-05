import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_span_singleton_eq_map_flip (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (n : N) :
    Submodule.map₂ f s (span R {n}) = map (f.flip n) s := by rw [← Submodule.map₂_span_singleton_eq_map, Submodule.map₂_flip]

