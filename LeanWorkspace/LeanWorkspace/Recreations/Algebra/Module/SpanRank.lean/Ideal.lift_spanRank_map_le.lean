import Mathlib

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

theorem Ideal.lift_spanRank_map_le (f : R →+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank ≤ Cardinal.lift.{v} I.spanRank := by
  rw [← Submodule.generators_card I, Submodule.lift_spanRank_le_iff_exists_span_set_card_le]
  refine ⟨f '' I.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun s ⟨r, hr, hfr⟩ ↦
    hfr ▸ mem_map_of_mem _ <| Submodule.span_generators I ▸ subset_span hr)) ?_⟩
  refine map_le_of_le_comap (fun r hr ↦ ?_)
  simp only [submodule_span_eq, mem_comap]
  rw [← map_span, ← submodule_span_eq, Submodule.span_generators]
  exact mem_map_of_mem f hr

