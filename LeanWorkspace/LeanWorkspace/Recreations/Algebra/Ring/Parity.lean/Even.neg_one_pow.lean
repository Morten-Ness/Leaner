import Mathlib

variable {F α β : Type*}

variable [Monoid α] [HasDistribNeg α] {n : ℕ} {a : α}

theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]

