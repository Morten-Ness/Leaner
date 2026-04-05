import Mathlib

variable {α β : Type*}

theorem nsmul_cons {s : Multiset α} (n : ℕ) (a : α) :
    n • (a ::ₘ s) = n • ({a} : Multiset α) + n • s := by
  rw [← singleton_add, nsmul_add]

