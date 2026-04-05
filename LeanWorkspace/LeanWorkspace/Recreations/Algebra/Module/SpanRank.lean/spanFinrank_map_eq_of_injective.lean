import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanFinrank_map_eq_of_injective [RingHomSurjective σ] (f : M →ₛₗ[σ] L)
    (hf : Function.Injective f) {p : Submodule R M} :
    (p.map f).spanFinrank = p.spanFinrank := by
  rw [Submodule.spanFinrank, Submodule.spanFinrank, ← Cardinal.toNat_lift.{u, v},
    ← Cardinal.toNat_lift.{v, u}, Submodule.lift_spanRank_map_eq_of_injective f hf p]

