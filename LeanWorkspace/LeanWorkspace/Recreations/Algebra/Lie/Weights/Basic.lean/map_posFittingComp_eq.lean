import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (LieModule.posFittingComp R L M).map e = LieModule.posFittingComp R L M₂ := by
  refine le_antisymm (LieModule.map_posFittingComp_le _) ?_
  suffices LieModule.posFittingComp R L M₂ = ((LieModule.posFittingComp R L M₂).map (e.symm : M₂ →ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (LieModule.map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert LieSubmodule.map_id
  ext
  simp

