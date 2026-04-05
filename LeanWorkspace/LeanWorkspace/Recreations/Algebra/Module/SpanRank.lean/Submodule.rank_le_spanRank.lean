import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem Submodule.rank_le_spanRank [StrongRankCondition R] :
    Module.rank R M ≤ (⊤ : Submodule R M).spanRank := by
  rw [Module.rank, Submodule.spanRank]
  refine ciSup_le' (fun ι ↦ (le_ciInf fun s ↦ ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

