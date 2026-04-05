import Mathlib

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

theorem le_spanRank_restrictScalars (N : Submodule S M) :
    N.spanRank ≤ (N.restrictScalars R).spanRank := by
  obtain ⟨s, hs, e⟩ := Submodule.exists_span_set_card_eq_spanRank (N.restrictScalars R)
  obtain rfl : span S s = N :=
    le_antisymm (span_le.mpr (span_le.mp e.le :)) (e.ge.trans (span_le_restrictScalars R S s))
  grw [← hs, Submodule.spanRank_span_le_card]

