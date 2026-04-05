import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nsmul_eq [AddMonoid α] (h : Function.Periodic f c) (n : ℕ) : f (n • c) = f 0 := (h.nsmul n).eq

