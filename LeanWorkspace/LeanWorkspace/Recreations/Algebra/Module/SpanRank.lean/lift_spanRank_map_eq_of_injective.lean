import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem lift_spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M →ₛₗ[σ] L)
    (hf : Function.Injective f) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank = Cardinal.lift.{v} p.spanRank := by
  refine (Submodule.lift_spanRank_map_le f p).antisymm ?_
  obtain ⟨s, hs, e⟩ := Submodule.exists_span_set_card_eq_spanRank (p.map f)
  obtain ⟨s, rfl⟩ : ∃ y, f '' y = s := Set.subset_range_iff_exists_image_eq.mp
    ((subset_span.trans e.le).trans LinearMap.map_le_range)
  obtain rfl : span R s = p := by simpa [(map_injective_of_injective hf).eq_iff] using e
  grw [← hs, Cardinal.mk_image_eq_lift _ _ hf, Cardinal.lift_le, Submodule.spanRank_span_le_card]

