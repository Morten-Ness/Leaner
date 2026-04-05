import Mathlib

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

