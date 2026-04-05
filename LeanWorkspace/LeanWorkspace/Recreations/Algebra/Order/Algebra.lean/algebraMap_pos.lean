import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable [Nontrivial β]

variable (β) [SMulPosStrictMono α β]

theorem algebraMap_pos {a : α} (ha : 0 < a) : 0 < algebraMap α β a := by
  simpa using algebraMap_strictMono β ha

