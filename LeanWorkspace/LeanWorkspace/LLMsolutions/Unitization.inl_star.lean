import Mathlib

variable {R A : Type*}

theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    Unitization.inl (star r) = star (Unitization.inl r : Unitization R A) := by
  ext
  · rfl
  · simp [Unitization.inl]
