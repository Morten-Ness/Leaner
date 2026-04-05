import Mathlib

variable {R K : Type*}

theorem IsRat.natFloor {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsRat r (Int.negOfNat n) d) : IsNat ⌊r⌋₊ 0 := by
  rcases h with ⟨hd, rfl⟩
  constructor
  rw [Nat.cast_zero, Nat.floor_eq_zero]
  exact lt_of_le_of_lt (by simp [mul_nonneg]) one_pos

