import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem isLieAbelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤ := LieModule.isTrivial_iff_max_triv_eq_top R L L

