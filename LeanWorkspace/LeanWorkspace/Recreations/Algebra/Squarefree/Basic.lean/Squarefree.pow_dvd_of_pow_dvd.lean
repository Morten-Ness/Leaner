import Mathlib

variable {R : Type*}

theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : ℕ}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

