import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem mem_lieSpan {x : M} : x ∈ LieSubmodule.lieSpan R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N := by
  rw [← SetLike.mem_coe, LieSubmodule.lieSpan, LieSubmodule.coe_sInf]
  exact mem_iInter₂

