import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanFinrank_map_le_of_fg [RingHomSurjective σ] (f : M →ₛₗ[σ] L) {p : Submodule R M}
    (hp : p.FG) : (p.map f).spanFinrank ≤ p.spanFinrank := by
  rw [← (hp.map f).spanRank_le_iff, ← Cardinal.lift_le.{u}, Cardinal.lift_natCast,
    ← Cardinal.lift_natCast.{v}, ← hp.spanRank_eq_spanFinrank]
  exact Submodule.lift_spanRank_map_le p f

