import Mathlib

variable {R A : Type*}

theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) := Unitization.ext (by simp only [Unitization.fst_star, star_zero, Unitization.fst_inr]) rfl

