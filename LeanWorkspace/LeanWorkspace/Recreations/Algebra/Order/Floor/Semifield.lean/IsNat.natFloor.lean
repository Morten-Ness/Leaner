import Mathlib

variable {R K : Type*}

theorem IsNat.natFloor {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : ℕ) : IsNat r m → IsNat (⌊r⌋₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

