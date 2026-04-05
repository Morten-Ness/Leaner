import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem coe_iInf {ι} (p : ι → LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, LieSubmodule.coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

