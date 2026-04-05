import Mathlib

variable {R : Type u}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

theorem pow_pos [NoZeroDivisors R] {a : R} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := pos_iff_ne_zero.2 <| pow_ne_zero _ ha.ne'

protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono R] {a b c d : R} (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact CanonicallyOrderedAdd.mul_pos ((zero_le _).trans_lt hab) hcd
  · exact mul_lt_mul_of_pos' hab hcd hc ((zero_le _).trans_lt hab)

