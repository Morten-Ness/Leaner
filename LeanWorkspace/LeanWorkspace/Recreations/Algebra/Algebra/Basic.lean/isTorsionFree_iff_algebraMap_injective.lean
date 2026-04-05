import Mathlib

open scoped Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable [IsDomain R] [IsDomain A]

theorem isTorsionFree_iff_algebraMap_injective : IsTorsionFree R A ↔ Function.Injective (algebraMap R A) := by
  rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]

