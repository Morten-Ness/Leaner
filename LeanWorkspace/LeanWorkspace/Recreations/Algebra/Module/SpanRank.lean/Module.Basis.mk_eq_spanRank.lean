import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem Module.Basis.mk_eq_spanRank [RankCondition R] {ι : Type*} (v : Module.Basis ι R M) :
    #(Set.range v) = (⊤ : Submodule R M).spanRank := by
  rw [← v.span_eq, Submodule.spanRank_span_of_linearIndepOn]
  exact v.linearIndependent.linearIndepOn_id

