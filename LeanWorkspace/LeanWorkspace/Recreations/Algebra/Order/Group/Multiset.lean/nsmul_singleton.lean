import Mathlib

variable {α β : Type*}

theorem nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a := by
  rw [← replicate_one, Multiset.nsmul_replicate, mul_one]

