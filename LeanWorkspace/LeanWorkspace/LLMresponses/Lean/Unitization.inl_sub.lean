import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) :
    (Unitization.inl (r₁ - r₂) : Unitization R A) = Unitization.inl r₁ - Unitization.inl r₂ := by
  simp [sub_eq_add_neg]
