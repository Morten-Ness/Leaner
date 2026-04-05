import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable (β) [SMulPosMono α β]

theorem algebraMap_nonneg {a : α} (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by
  simpa using algebraMap_mono β ha

