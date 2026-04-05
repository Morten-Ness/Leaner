import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' := by
  rw [← LieSubmodule.mem_toSubmodule, ← LieSubmodule.mem_toSubmodule, ← LieSubmodule.mem_toSubmodule, LieSubmodule.inf_toSubmodule,
    Submodule.mem_inf]

