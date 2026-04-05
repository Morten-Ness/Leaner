import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem lift_spanRank_map_le [RingHomSurjective σ] (f : M →ₛₗ[σ] L) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank ≤ Cardinal.lift.{v} p.spanRank := by
  rw [← Submodule.generators_card p, Submodule.lift_spanRank_le_iff_exists_span_set_card_le]
  exact ⟨f '' p.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun n ⟨m, hm, h⟩ ↦
    ⟨m, Submodule.span_generators p ▸ subset_span hm, h⟩)) (by simp [Submodule.span_generators])⟩

