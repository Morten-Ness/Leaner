import Mathlib

variable {R : Type*}

theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : ℕ}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 ≤ n := by lia
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

