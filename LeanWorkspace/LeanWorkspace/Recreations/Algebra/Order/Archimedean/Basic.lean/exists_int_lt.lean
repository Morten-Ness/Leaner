import Mathlib

variable {G M R K : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_int_lt (x : R) : ∃ n : ℤ, (n : R) < x := let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

