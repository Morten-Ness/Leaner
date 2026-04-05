import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.int_mul [NonAssocRing α] (h : Function.Periodic f c) (n : ℤ) :
    Function.Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n

