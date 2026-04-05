import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem Module.finrank_eq_spanFinrank_of_free [StrongRankCondition R] [Module.Free R M] :
    Module.finrank R M = (⊤ : Submodule R M).spanFinrank := by
  simp [Module.finrank, Submodule.spanFinrank, Submodule.rank_eq_spanRank_of_free]

