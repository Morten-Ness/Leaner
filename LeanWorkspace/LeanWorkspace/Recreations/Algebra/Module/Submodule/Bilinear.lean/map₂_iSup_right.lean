import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_iSup_right (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (t : ι → Submodule R N) :
    Submodule.map₂ f s (⨆ i, t i) = ⨆ i, Submodule.map₂ f s (t i) := by
  suffices Submodule.map₂ f (span R s) (⨆ i, span R (t i : Set N)) = ⨆ i, Submodule.map₂ f (span R s) (span R (t i)) by
    simpa only [span_eq] using this
  simp_rw [Submodule.map₂_span_span, ← span_iUnion, Submodule.map₂_span_span, Set.image2_iUnion_right]

