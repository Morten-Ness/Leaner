import Mathlib

variable {G M R K : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_int_gt (x : R) : ∃ n : ℤ, x < n := let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

