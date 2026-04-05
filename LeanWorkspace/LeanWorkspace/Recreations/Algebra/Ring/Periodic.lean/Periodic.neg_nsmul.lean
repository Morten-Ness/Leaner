import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.neg_nsmul [AddGroup α] (h : Function.Periodic f c) (n : ℕ) : Function.Periodic f (-(n • c)) := (h.nsmul n).neg

