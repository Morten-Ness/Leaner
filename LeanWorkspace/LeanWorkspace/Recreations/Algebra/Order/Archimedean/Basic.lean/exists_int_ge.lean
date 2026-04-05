import Mathlib

variable {G M R K : Type*}

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_int_ge (x : R) : ∃ n : ℤ, x ≤ n := let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

