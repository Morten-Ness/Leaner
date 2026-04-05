import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem Submodule.rank_eq_spanRank_of_free [Module.Free R M] [StrongRankCondition R] :
    Module.rank R M = (⊤ : Submodule R M).spanRank := by
  haveI := nontrivial_of_invariantBasisNumber R
  obtain ⟨I, B⟩ := ‹Module.Free R M›
  rw [← Module.Basis.mk_eq_rank'' B, ← Module.Basis.mk_eq_spanRank B, ← Cardinal.lift_id #(Set.range B),
    Cardinal.mk_range_eq_of_injective B.injective, Cardinal.lift_id _]

