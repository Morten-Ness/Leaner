import Mathlib

open scoped Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable [IsDomain R] [IsDomain A]

theorem isTorsionFree_iff_faithfulSMul : IsTorsionFree R A ↔ FaithfulSMul R A := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

