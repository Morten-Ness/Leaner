import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem mem_center_iff_val_mem_range_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (Matrix.scalar n) := by
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simpa [Units.ext_iff, ← ha] using (scalar_commute a (mul_comm a ·) h.val).symm

