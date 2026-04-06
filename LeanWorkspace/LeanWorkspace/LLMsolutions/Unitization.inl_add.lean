import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (Unitization.inl (r₁ + r₂) : Unitization R A) = Unitization.inl r₁ + Unitization.inl r₂ := by
  ext <;> simp [Unitization.inl]
