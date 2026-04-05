import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact Squarefree.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

