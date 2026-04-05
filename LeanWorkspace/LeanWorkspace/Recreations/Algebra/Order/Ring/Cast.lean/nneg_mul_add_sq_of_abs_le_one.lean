import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem nneg_mul_add_sq_of_abs_le_one (n : ℤ) (hx : |x| ≤ 1) : (0 : R) ≤ n * x + n * n := by
  have hnx : 0 < n → 0 ≤ x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (Int.cast_one_le_of_pos hn)
    rwa [neg_add_cancel] at this
  have hnx' : n < 0 → x + n ≤ 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (Int.cast_le_neg_one_of_neg hn)
    rwa [add_neg_cancel] at this
  rw [← mul_add, mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨mod_cast h.le, hnx h⟩

