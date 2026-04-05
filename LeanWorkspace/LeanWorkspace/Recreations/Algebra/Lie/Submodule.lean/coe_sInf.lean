import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s ∈ S, (s : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, LieSubmodule.sInf_toSubmodule, Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_setOf_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, LieSubmodule.mem_toSubmodule]

