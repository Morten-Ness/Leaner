import Mathlib

variable {R K : Type*}

theorem IsInt.natFloor {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : ℕ) : IsInt r (.negOfNat m) → IsNat (⌊r⌋₊) 0 := by
  rintro ⟨⟨⟩⟩
  exact ⟨Nat.floor_of_nonpos <| by simp⟩

