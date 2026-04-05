import Mathlib

variable {α β : Type*}

variable [NonUnitalCommRing α]

theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y) using 1
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

