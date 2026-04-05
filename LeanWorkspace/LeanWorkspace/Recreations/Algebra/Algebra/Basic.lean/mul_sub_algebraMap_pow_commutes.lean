import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, Algebra.mul_sub_algebraMap_commutes, mul_assoc, ih, ← mul_assoc]

