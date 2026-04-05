import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

theorem isOrderedModule_iff_algebraMap_mono [PosMulMono β] [MulPosMono β] :
    IsOrderedModule α β ↔ Monotone (algebraMap α β) := by
  simp [isOrderedModule_iff_smul_one_mono, Algebra.smul_def]

