import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_eq_zero_or_add_one_sub_ceil (a : R) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : R) := by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : R) = ⌊a⌋ + 1 by
    rw [this, ← Int.self_sub_fract]
    abel
  norm_cast
  rw [Int.ceil_eq_iff]
  refine ⟨?_, _root_.le_of_lt <| by simp⟩
  rw [cast_add, cast_one, add_tsub_cancel_right, ← Int.self_sub_fract a, sub_lt_self_iff]
  exact ha.symm.lt_of_le (Int.fract_nonneg a)

