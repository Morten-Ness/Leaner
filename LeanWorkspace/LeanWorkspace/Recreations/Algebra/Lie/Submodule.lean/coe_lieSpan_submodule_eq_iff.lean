import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem coe_lieSpan_submodule_eq_iff {p : Submodule R M} :
    (LieSubmodule.lieSpan R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, LieSubmodule.mem_toSubmodule]; exact lie_mem _ (LieSubmodule.subset_lieSpan hm)
  · rw [← LieSubmodule.toSubmodule_mk p @h, LieSubmodule.coe_toSubmodule, LieSubmodule.toSubmodule_inj, LieSubmodule.lieSpan_eq]

