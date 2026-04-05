import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_iInf {ι} (p : ι → LieSubmodule R L M) {x} : x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, LieSubmodule.coe_iInf, Set.mem_iInter]; rfl

