import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ v ≠ 0, W = span K {v} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv

