import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem lift_spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} :
    Cardinal.lift.{v} p.spanRank ≤ a ↔ ∃ s : Set M, Cardinal.lift.{v} #s ≤ a ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := Submodule.exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact fun ⟨s, ⟨h₁, h₂⟩⟩ ↦ h₂.symm ▸ (Cardinal.lift_le.mpr (Submodule.spanRank_span_le_card s)).trans h₁

