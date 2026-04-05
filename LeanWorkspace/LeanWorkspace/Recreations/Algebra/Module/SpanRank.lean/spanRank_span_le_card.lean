import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank ≤ #s := by
  rw [Submodule.spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'

