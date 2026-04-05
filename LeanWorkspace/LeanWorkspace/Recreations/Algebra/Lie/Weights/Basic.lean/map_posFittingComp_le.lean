import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem map_posFittingComp_le :
    (LieModule.posFittingComp R L M).map f ≤ LieModule.posFittingComp R L M₂ := by
  rw [LieModule.posFittingComp, LieModule.posFittingComp, LieSubmodule.map_iSup]
  refine iSup_mono fun y ↦ LieSubmodule.map_le_iff_le_comap.mpr fun m hm ↦ ?_
  simp only [LieModule.mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, LieModule.mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
  rw [LieModule.toEnd_pow_apply_map, hn]

