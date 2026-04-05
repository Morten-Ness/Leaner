import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG := by
  rw [Submodule.spanRank, Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
      Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ?_, s.2⟩
    simpa [← hs] using h
  · rintro ⟨s, hs₁, hs₂⟩
    exact (ciInf_le' _ ⟨s, hs₂⟩).trans_lt (by simpa)

