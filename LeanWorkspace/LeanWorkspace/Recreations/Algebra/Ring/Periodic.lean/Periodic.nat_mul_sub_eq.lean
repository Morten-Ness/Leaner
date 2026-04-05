import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nat_mul_sub_eq [NonAssocRing α] (h : Function.Periodic f c) (n : ℕ) :
    f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

