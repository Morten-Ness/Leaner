import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_span_of_linearIndepOn [RankCondition R] (s : Set M) (hs : LinearIndepOn R id s) :
    (span R s).spanRank = #s := by
  simp [← Submodule.spanRank_span_range_of_linearIndependent Subtype.val_injective hs]

