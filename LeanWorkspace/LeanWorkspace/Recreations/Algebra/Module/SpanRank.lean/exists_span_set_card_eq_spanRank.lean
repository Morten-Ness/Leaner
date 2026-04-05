import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem exists_span_set_card_eq_spanRank (p : Submodule R M) :
    ∃ s : Set M, #s = p.spanRank ∧ span R s = p := by
  rw [Submodule.spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
    Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

