import Mathlib

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

theorem spanRank_restrictScalars_eq (H : Function.Surjective (algebraMap R S))
    (N : Submodule S M) : (N.restrictScalars R).spanRank = N.spanRank := by
  refine N.le_spanRank_restrictScalars.antisymm' ?_
  obtain ⟨s, hs, rfl⟩ := N.exists_span_set_card_eq_spanRank
  grw [restrictScalars_span R S H s, ← hs, Submodule.spanRank_span_le_card]

