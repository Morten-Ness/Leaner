import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.neg_nat_mul [NonAssocRing α] (h : Function.Periodic f c) (n : ℕ) : Function.Periodic f (-(n * c)) := (h.nat_mul n).neg

