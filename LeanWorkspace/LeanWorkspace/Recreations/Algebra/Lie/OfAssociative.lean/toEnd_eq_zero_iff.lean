import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem toEnd_eq_zero_iff [IsFaithful R L M] {x : L} :
    toEnd R L M x = 0 ↔ x = 0 := by
  rw [← (toEnd R L M).toLinearMap.map_zero]
  exact LieModule.toEnd_eq_iff R L M

