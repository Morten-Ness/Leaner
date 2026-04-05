import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable (β) [SMulPosMono α β]

theorem algebraMap_mono : Monotone (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_mono (α := α) β

