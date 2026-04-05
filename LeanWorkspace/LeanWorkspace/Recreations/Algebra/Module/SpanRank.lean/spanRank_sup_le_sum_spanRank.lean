import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  apply (Submodule.FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := Submodule.exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := Submodule.exists_span_set_card_eq_spanRank q
  exact ⟨sp ∪ sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩

