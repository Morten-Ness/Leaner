import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable [Nontrivial β]

variable (β) [SMulPosStrictMono α β]

theorem algebraMap_strictMono : StrictMono (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_strictMono (α := α) β

