import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem sSup_image_lieSpan_singleton : sSup ((fun x ↦ LieSubmodule.lieSpan R L {x}) '' N) = N := by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← LieSubmodule.toSubmodule_le_toSubmodule, LieSubmodule.sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm ↦ Submodule.mem_sSup.mpr fun N' hN' ↦ ?_
  replace hN' : ∀ m ∈ N, LieSubmodule.lieSpan R L {m} ≤ N' := by simpa using hN'
  exact hN' _ hm (LieSubmodule.subset_lieSpan rfl)

