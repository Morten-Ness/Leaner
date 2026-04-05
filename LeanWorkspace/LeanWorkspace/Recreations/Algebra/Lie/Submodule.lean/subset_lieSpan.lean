import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem subset_lieSpan : s ⊆ LieSubmodule.lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe, LieSubmodule.mem_lieSpan]
  intro N hN
  exact hN hm

