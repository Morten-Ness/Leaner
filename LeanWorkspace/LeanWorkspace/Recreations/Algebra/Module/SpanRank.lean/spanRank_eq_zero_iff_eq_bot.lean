import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (Submodule.FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [Submodule.spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

