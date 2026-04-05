import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : R) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [Nat.floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

