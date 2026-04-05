import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem ceil_add_natCast (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n := eq_of_forall_ge_iff fun b => by
    contrapose!
    rw [lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : R), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)

