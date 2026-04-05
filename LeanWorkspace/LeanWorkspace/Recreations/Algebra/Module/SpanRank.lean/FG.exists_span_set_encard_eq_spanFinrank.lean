import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := Submodule.exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := Submodule.fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard, ENat.card, Submodule.spanFinrank, hs₁, this]
  simp

