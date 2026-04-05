import Mathlib

variable {R : Type*} [CommSemiring R] {X : Type*}

theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]

