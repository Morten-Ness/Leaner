FAIL
import Mathlib

variable {R A : Type*}

theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) := by
  ext <;> simp [Unitization.inr, Unitization.star]
