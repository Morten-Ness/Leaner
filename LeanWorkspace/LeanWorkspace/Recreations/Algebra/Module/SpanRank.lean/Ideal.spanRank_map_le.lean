import Mathlib

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

theorem Ideal.spanRank_map_le (f : R →+* S) (I : Ideal R) : (I.map f).spanRank ≤ I.spanRank := by
  simpa using I.lift_spanRank_map_le f

