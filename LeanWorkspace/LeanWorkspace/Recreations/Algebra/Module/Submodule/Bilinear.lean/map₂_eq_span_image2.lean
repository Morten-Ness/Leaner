import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_eq_span_image2 (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    Submodule.map₂ f p q = span R (Set.image2 (fun m n => f m n) (p : Set M) (q : Set N)) := by
  rw [← Submodule.map₂_span_span, span_eq, span_eq]

