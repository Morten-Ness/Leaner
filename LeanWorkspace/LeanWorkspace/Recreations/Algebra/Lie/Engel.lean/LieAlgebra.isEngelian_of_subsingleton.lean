import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp

