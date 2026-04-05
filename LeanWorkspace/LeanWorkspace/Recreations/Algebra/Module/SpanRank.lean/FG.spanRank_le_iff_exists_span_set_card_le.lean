import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ s : Set M, #s ≤ a ∧ span R s = p := by
  convert Submodule.lift_spanRank_le_iff_exists_span_set_card_le p (a := a) <;> simp

