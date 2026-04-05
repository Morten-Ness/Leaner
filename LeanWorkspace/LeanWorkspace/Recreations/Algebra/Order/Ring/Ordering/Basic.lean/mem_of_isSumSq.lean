import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

