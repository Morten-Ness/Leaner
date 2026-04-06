FAIL
import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  let y : A := algebraMap R A r
  have hy : Commute x y := Algebra.commutes (r := r) x
  have hxy : Commute x (x - y) := by
    rw [sub_eq_add_neg]
    exact (Commute.refl x).add_right <| hy.neg_right
  simpa [y] using (hxy.pow_right n).eq
