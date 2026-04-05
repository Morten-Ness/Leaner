import Mathlib

variable {R A : Type*}

theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    Unitization.inl (star r) = star (Unitization.inl r : Unitization R A) := Unitization.ext rfl (by simp only [Unitization.snd_star, star_zero, Unitization.snd_inl])

