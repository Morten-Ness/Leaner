import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nat_mul [NonAssocSemiring α] (h : Function.Periodic f c) (n : ℕ) : Function.Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n

