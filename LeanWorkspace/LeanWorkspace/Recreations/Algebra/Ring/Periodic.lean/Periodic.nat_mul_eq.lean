import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nat_mul_eq [NonAssocSemiring α] (h : Function.Periodic f c) (n : ℕ) : f (n * c) = f 0 := (h.nat_mul n).eq

