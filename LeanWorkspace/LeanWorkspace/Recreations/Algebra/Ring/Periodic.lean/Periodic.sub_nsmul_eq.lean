import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_nsmul_eq [AddGroup α] (h : Function.Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

