import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_iSup_left (f : M →ₗ[R] N →ₗ[R] P) (s : ι → Submodule R M) (t : Submodule R N) :
    Submodule.map₂ f (⨆ i, s i) t = ⨆ i, Submodule.map₂ f (s i) t := by
  suffices Submodule.map₂ f (⨆ i, span R (s i : Set M)) (span R t) = ⨆ i, Submodule.map₂ f (span R (s i)) (span R t) by
    simpa only [span_eq] using this
  simp_rw [Submodule.map₂_span_span, ← span_iUnion, Submodule.map₂_span_span, Set.image2_iUnion_left]

