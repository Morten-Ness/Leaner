import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem submodule_strictAnti : StrictAnti (FiniteArchimedeanClass.submodule K (M := M)) := addSubgroup_strictAnti

