import Mathlib

variable {G M R K : Type*}

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_int_le (x : R) : ∃ n : ℤ, n ≤ x := let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

