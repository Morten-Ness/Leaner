import Mathlib

variable {G M R K : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_floor (x : R) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : R) ≤ x := by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

