import Mathlib

variable {R : Type u} {α : Type*}

variable [CommSemiring R] [LinearOrder R] {a d : R}

theorem two_mul_le_add_of_sq_eq_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  conv_rhs => rw [← pow_two]
  convert four_mul_le_sq_add a b using 1
  rw [mul_mul_mul_comm, two_mul, two_add_two_eq_four, ← pow_two, ht, mul_assoc]

